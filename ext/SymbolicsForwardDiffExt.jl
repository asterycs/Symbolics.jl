module SymbolicsForwardDiffExt

using ForwardDiff
using Symbolics

const AMBIGUOUS_TYPES = (Num,)

for (M, f, arity) in ForwardDiff.DiffRules.diffrules(filter_modules = nothing)
    if (M, f) in ((:Base, :^), (:NaNMath, :pow), (:Base, :/), (:Base, :+), (:Base, :-), (:Base, :sin), (:Base, :cos))
        continue  # Skip methods which we define elsewhere.
    elseif !(isdefined(@__MODULE__, M) && isdefined(getfield(@__MODULE__, M), f))
        continue  # Skip rules for methods not defined in the current scope
    end
    if arity == 1
        # no-op
    elseif arity == 2
        eval(ForwardDiff.binary_dual_definition(M, f, AMBIGUOUS_TYPES))
    else
        # error("ForwardDiff currently only knows how to autogenerate Dual definitions for unary and binary functions.")
        # However, the presence of N-ary rules need not cause any problems here, they can simply be ignored.
    end
end


# Predicates #
#------------#

for pred in ForwardDiff.BINARY_PREDICATES
    @eval begin
        ForwardDiff.@define_binary_dual_op(
            Base.$(pred),
            $(pred)(value(x), value(y)),
            $(pred)(value(x), y),
            $(pred)(x, value(y)),
            $AMBIGUOUS_TYPES
        )
    end
end

###################################
# General Mathematical Operations #
###################################

for (M, f, arity) in ForwardDiff.DiffRules.diffrules(filter_modules = nothing)
    if (M, f) in ((:Base, :^), (:NaNMath, :pow), (:Base, :/), (:Base, :+), (:Base, :-), (:Base, :sin), (:Base, :cos))
        continue  # Skip methods which we define elsewhere.
    elseif !(isdefined(@__MODULE__, M) && isdefined(getfield(@__MODULE__, M), f))
        continue  # Skip rules for methods not defined in the current scope
    end
    if arity == 1
        eval(ForwardDiff.unary_dual_definition(M, f))
    elseif arity == 2
        eval(ForwardDiff.binary_dual_definition(M, f, AMBIGUOUS_TYPES))
    else
        # error("ForwardDiff currently only knows how to autogenerate Dual definitions for unary and binary functions.")
        # However, the presence of N-ary rules need not cause any problems here, they can simply be ignored.
    end
end

#################
# Special Cases #
#################

# +/- #
#-----#

@eval begin
    ForwardDiff.@define_binary_dual_op(
        Base.:+,
        begin
            vx, vy = value(x), value(y)
            Dual{Txy}(vx + vy, partials(x) + partials(y))
        end,
        Dual{Tx}(value(x) + y, partials(x)),
        Dual{Ty}(x + value(y), partials(y)),
        $AMBIGUOUS_TYPES
    )
end

@eval begin
    ForwardDiff.@define_binary_dual_op(
        Base.:-,
        begin
            vx, vy = value(x), value(y)
            Dual{Txy}(vx - vy, partials(x) - partials(y))
        end,
        Dual{Tx}(value(x) - y, partials(x)),
        Dual{Ty}(x - value(y), -partials(y)),
        $AMBIGUOUS_TYPES
    )
end

# / #
#---#

# We can't use the normal diffrule autogeneration for this because (x/y) === (x * (1/y))
# doesn't generally hold true for floating point; see issue #264
@eval begin
    ForwardDiff.@define_binary_dual_op(
        Base.:/,
        begin
            vx, vy = value(x), value(y)
            Dual{Txy}(vx / vy, _div_partials(partials(x), partials(y), vx, vy))
        end,
        Dual{Tx}(value(x) / y, partials(x) / y),
        begin
            v = value(y)
            divv = x / v
            Dual{Ty}(divv, -(divv / v) * partials(y))
        end,
        $AMBIGUOUS_TYPES
    )
end

# exponentiation #
#----------------#

for f in (:(Base.:^), :(ForwardDiff.NaNMath.pow))
    @eval begin
        ForwardDiff.@define_binary_dual_op(
            $f,
            begin
                vx, vy = value(x), value(y)
                expv = ($f)(vx, vy)
                powval = vy * ($f)(vx, vy - 1)
                if isconstant(y)
                    logval = one(expv)
                elseif iszero(vx) && vy > 0
                    logval = zero(vx)
                else
                    logval = expv * log(vx)
                end
                new_partials = _mul_partials(partials(x), partials(y), powval, logval)
                return Dual{Txy}(expv, new_partials)
            end,
            begin
                v = value(x)
                expv = ($f)(v, y)
                if y == zero(y) || iszero(partials(x))
                    new_partials = zero(partials(x))
                else
                    new_partials = partials(x) * y * ($f)(v, y - 1)
                end
                return Dual{Tx}(expv, new_partials)
            end,
            begin
                v = value(y)
                expv = ($f)(x, v)
                deriv = (iszero(x) && v > 0) ? zero(expv) : expv*log(x)
                return Dual{Ty}(expv, deriv * partials(y))
            end,
            $AMBIGUOUS_TYPES
        )
    end
end

# hypot #
#-------#

@eval begin
    ForwardDiff.@define_ternary_dual_op(
        Base.hypot,
        calc_hypot(x, y, z, Txyz),
        calc_hypot(x, y, z, Txy),
        calc_hypot(x, y, z, Txz),
        calc_hypot(x, y, z, Tyz),
        calc_hypot(x, y, z, Tx),
        calc_hypot(x, y, z, Ty),
        calc_hypot(x, y, z, Tz),
        $AMBIGUOUS_TYPES
    )
end

# fma #
#-----#

@eval begin
    ForwardDiff.@define_ternary_dual_op(
        Base.fma,
        calc_fma_xyz(x, y, z),                         # xyz_body
        calc_fma_xy(x, y, z),                          # xy_body
        calc_fma_xz(x, y, z),                          # xz_body
        Base.fma(y, x, z),                             # yz_body
        Dual{Tx}(fma(value(x), y, z), partials(x) * y), # x_body
        Base.fma(y, x, z),                              # y_body
        Dual{Tz}(fma(x, y, value(z)), partials(z)),     # z_body
        $AMBIGUOUS_TYPES
    )
end

# muladd #
#--------#

@eval begin
    ForwardDiff.@define_ternary_dual_op(
        Base.muladd,
        calc_muladd_xyz(x, y, z),                         # xyz_body
        calc_muladd_xy(x, y, z),                          # xy_body
        calc_muladd_xz(x, y, z),                          # xz_body
        Base.muladd(y, x, z),                             # yz_body
        Dual{Tx}(muladd(value(x), y, z), partials(x) * y), # x_body
        Base.muladd(y, x, z),                             # y_body
        Dual{Tz}(muladd(x, y, value(z)), partials(z)),     # z_body
        $AMBIGUOUS_TYPES
    )
end

end
