"""Implementation of the asymptotic analysis of polynomials."""

from typing import Literal
from expr import Expr, Mono, Exp, Scl, Add, Sub, Mul, equals

type Asymptotic = Literal["bottom", "top"] | tuple[float, float]


def asymptotic(poly: Expr) -> Asymptotic:
    """Return the asymptotic analysis of the polynomial `poly`."""
    if isinstance(poly, Mono):
        return (1.0, poly.r)

    if isinstance(poly, Exp):
        return "top"

    if isinstance(poly, Scl):
        if equals(poly.c, 0.0):
            return "bottom"

        sub: Asymptotic = asymptotic(poly.f)
        if sub in ("bottom", "top"):
            return sub

        assert isinstance(sub, tuple) and len(sub) == 2
        return (sub[0] * poly.c, sub[1])

    if isinstance(poly, (Add, Sub)):
        l_asymp: Asymptotic = asymptotic(poly.l)
        r_asymp: Asymptotic = asymptotic(poly.r)
        if l_asymp == "top" or r_asymp == "top":
            return "top"
        if l_asymp == "bottom":
            return r_asymp
        if r_asymp == "bottom":
            return l_asymp

        assert (
            isinstance(l_asymp, tuple)
            and isinstance(r_asymp, tuple)
            and len(l_asymp) == 2
            and len(r_asymp) == 2
        )

        if equals(l_asymp[1], r_asymp[1]):
            return (
                (
                    (l_asymp[0] + r_asymp[0])
                    if isinstance(poly, Add)
                    else (l_asymp[0] - r_asymp[0])
                ),
                l_asymp[1],
            )
        if l_asymp[1] > r_asymp[1]:
            return l_asymp
        return r_asymp

    if isinstance(poly, Mul):
        l_asymp = asymptotic(poly.l)
        r_asymp = asymptotic(poly.r)
        if l_asymp == "bottom" or r_asymp == "bottom":
            return "bottom"
        if l_asymp == "top" or r_asymp == "top":
            return "top"

        assert (
            isinstance(l_asymp, tuple)
            and isinstance(r_asymp, tuple)
            and len(l_asymp) == 2
            and len(r_asymp) == 2
        )
        return (l_asymp[0] * r_asymp[0], l_asymp[1] + r_asymp[1])

    raise NotImplementedError(f"Unsupported polynomial type: {type(poly)}")


def asymptotic_eq(imp1: Asymptotic, imp2: Asymptotic) -> bool:
    """Return whether the asymptotic analyses `imp1` and `imp2` are equal."""
    if isinstance(imp1, str) or isinstance(imp2, str):
        return imp1 == imp2

    assert (
        isinstance(imp1, tuple)
        and isinstance(imp2, tuple)
        and len(imp1) == 2
        and len(imp2) == 2
    )
    return equals(imp1[0], imp2[0]) and equals(imp1[1], imp2[1])
