"""Implementation of the asymptotic analysis of polynomials."""

from typing import Literal
from polynomials import IntFunc, Mono, Exp, Scl, Add, Sub, Mul, equals

type Asymptotic = Literal["bottom", "top"] | tuple[float | Literal["coeff_top"], float]


def asymptotic(poly: IntFunc) -> Asymptotic:
    """Return the asymptotic analysis of the polynomial `poly`."""
    if isinstance(poly, Mono):
        return (1.0, poly.r)

    if isinstance(poly, Exp):
        return "top"

    if isinstance(poly, Scl):
        if equals(poly.c, 0.0):
            return "bottom"

        sub: Asymptotic = asymptotic(poly.f)
        if sub in ["bottom", "top"]:
            return sub

        assert isinstance(sub, tuple) and len(sub) == 2
        if sub[0] == "coeff_top":
            return sub

        return (sub[0] * poly.c, sub[1])

    if isinstance(poly, Add) or isinstance(poly, Sub):
        l: Asymptotic = asymptotic(poly.l)
        r: Asymptotic = asymptotic(poly.r)
        if l == "top" or r == "top":
            return "top"
        if l == "bottom":
            return r
        if r == "bottom":
            return l

        assert (
            isinstance(l, tuple)
            and isinstance(r, tuple)
            and len(l) == 2
            and len(r) == 2
        )

        if equals(l[1], r[1]):
            if l[0] == "coeff_top" or r[0] == "coeff_top":
                return ("coeff_top", l[1])
            return ((l[0] + r[0]) if isinstance(poly, Add) else (l[0] - r[0]), l[1])
        if l[1] > r[1]:
            return l
        return r

    if isinstance(poly, Mul):
        l: Asymptotic = asymptotic(poly.l)
        r: Asymptotic = asymptotic(poly.r)
        if l == "bottom" or r == "bottom":
            return "bottom"
        if l == "top" or r == "top":
            return "top"

        assert (
            isinstance(l, tuple)
            and isinstance(r, tuple)
            and len(l) == 2
            and len(r) == 2
        )

        if l[0] == "coeff_top" or r[0] == "coeff_top":
            return ("coeff_top", l[1] + r[1])
        return (l[0] * r[0], l[1] + r[1])

    raise NotImplementedError(f"Unsupported polynomial type: {type(poly)}")


def asymptotic_eq(imp1: Asymptotic, imp2: Asymptotic) -> bool:
    """Return whether the asymptotic analyses `imp1` and `imp2` are equal."""
    if imp1 == imp2:
        return True

    if imp1 in ["bottom", "top"] or imp2 in ["bottom", "top"]:
        return False

    assert (
        isinstance(imp1, tuple)
        and isinstance(imp2, tuple)
        and len(imp1) == 2
        and len(imp2) == 2
    )

    if imp1[0] == "coeff_top" or imp2[0] == "coeff_top":
        return imp1[0] == imp2[0] and equals(imp1[1], imp2[1])

    return equals(imp1[0], imp2[0]) and equals(imp1[1], imp2[1])


def test(f_imp: IntFunc, ans: Asymptotic) -> None:
    """Test the asymptotic analysis of the polynomial `f_imp`."""
    imp: Asymptotic = asymptotic(f_imp)
    assert asymptotic_eq(imp, ans), f"Failed: {f_imp} -> {imp} != {ans}"
    print(f"Passed: {f_imp} -> {ans}")


if __name__ == "__main__":
    test(
        Mul(Add(Mono(1.0), Scl(2.0, Mono(0.0))), Sub(Scl(0.5, Mono(3.0)), Mono(2.0))),
        (0.5, 4.0),
    )
    test(Scl(0.0, Mono(1.0)), "bottom")
    test(Add(Mono(1.0), Exp()), "top")
