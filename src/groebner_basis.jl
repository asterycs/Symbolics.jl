import DynamicPolynomials
using Bijections

const DP = DynamicPolynomials
# extracting underlying polynomial and coefficient type from Polyforms
underlyingpoly(x::Number) = x
underlyingpoly(pf::PolyForm) = pf.p
coefftype(x::Number) = typeof(x)
coefftype(pf::PolyForm) = DP.coefficienttype(underlyingpoly(pf))

#=
Converts an array of symbolic polynomials
into an array of DynamicPolynomials.Polynomials
=#
function symbol_to_poly(sympolys::AbstractArray)
    @assert !isempty(sympolys) "Empty input."

    # standardize input
    stdsympolys = map(unwrap, sympolys)
    sort!(stdsympolys, lt=(<ₑ))

    pvar2sym = Bijections.Bijection{Any,Any}()
    sym2term = Dict{BasicSymbolic,Any}()
    polyforms = map(f -> PolyForm(f, pvar2sym, sym2term), stdsympolys)

    # Discover common coefficient type
    commontype = mapreduce(coefftype, promote_type, polyforms, init=Int)
    @assert commontype <: Union{Integer,Rational} "Only integer and rational coefficients are supported as input."

    # Convert all to DP.Polynomial, so that coefficients are of same type,
    # and constants are treated as polynomials
    # We also need this because Groebner does not support abstract types as input
    polynoms = Vector{DP.Polynomial{DP.Commutative{DP.CreationOrder}, DP.Graded{DP.LexOrder}, commontype}}(undef, length(sympolys))
    for (i, pf) in enumerate(polyforms)
        polynoms[i] = underlyingpoly(pf)
    end

    polynoms, pvar2sym, sym2term
end

#=
Converts an array of AbstractPolynomialLike`s into an array of
symbolic expressions mapping variables w.r.t pvar2sym
=#
function poly_to_symbol(polys, pvar2sym, sym2term, ::Type{T}) where {T}
    map(f -> PolyForm{T}(f, pvar2sym, sym2term), polys)
end

"""

groebner_basis(polynomials)

Computes a Groebner basis of the ideal generated by the given `polynomials`.
The basis is reduced, thus guaranteed to be unique.

# Example

```jldoctest
julia> using Symbolics

julia> @variables x y;

julia> groebner_basis([x*y^2 + x, x^2*y + y])
```

The coefficients in the resulting basis are in the same domain as for input polynomials.
Hence, if the coefficient becomes too large to be represented exactly, `DomainError` is thrown.

The algorithm is randomized, so the basis will be correct with high probability.

"""
function groebner_basis(polynomials)
    polynoms, pvar2sym, sym2term = symbol_to_poly(polynomials)

    basis = groebner(polynoms)

    # polynomials is nonemtpy
    T = symtype(first(polynomials))
    poly_to_symbol(basis, pvar2sym, sym2term, T)
end

"""

Do not document this for now.

is_groebner_basis(polynomials)

Checks whether the given `polynomials` forms a Groebner basis.

# Example

```jldoctest
julia> using Symbolics

julia> @variables x y;

julia> is_groebner_basis([x^2 - y^2, x*y^2 + x, y^3 + y])
```

"""
function is_groebner_basis(polynomials)
    polynoms, _, _ = symbol_to_poly(polynomials)
    isgroebner(polynoms)
end
