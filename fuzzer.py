"""Fuzzer to compare the full expansion and the asymptotic analysis."""

import random
from typing import Literal
from expr import DIGITS, EPS, equals, Expr, Mono, Exp, Scl, Add, Sub, Mul
from poly_expanded import TermPower, PolyExpanded, ZERO_LEADING
from asymptotic import asymptotic, Asymptotic


type AsymptoticTest = Literal["Tight", "Loose", "Incorrect"]


def test_asymptotic(lead: tuple[TermPower, float], asymp: Asymptotic) -> AsymptoticTest:
    """Tests whether the asymptotic analysis soundly approximates the leading term."""
    if asymp == "top":
        return "Tight" if lead[0].exp_power > 0 else "Loose"
    if asymp == "bottom":
        return "Tight" if lead == ZERO_LEADING else "Incorrect"
    if lead[0].exp_power > 0:
        return "Incorrect"

    if equals(lead[0].deg_power, asymp[1]):
        if equals(abs(lead[1]), abs(asymp[0])):
            return "Tight"
        if abs(lead[1]) < abs(asymp[0]):
            return "Loose"
        return "Incorrect"
    if lead[0].deg_power < asymp[1]:
        return "Loose"
    return "Incorrect"


def generate_poly(
    max_depth: int,
    no_exp: bool,
    same_const_prob: float,
    close_const_prob: float,
    consts_generated: list[float] | None = None,
) -> tuple[Expr, list[float]]:
    """Generate a random polynomial with a maximum depth of `max_depth`."""
    if not consts_generated:
        consts_generated = []

    def generate_constant() -> float:
        """Generate a random constant, possibly reusing a previously generated one."""
        random_value: float = random.random()
        res: float
        if consts_generated and random_value < same_const_prob:
            res = random.choice(consts_generated)
        elif consts_generated and random_value < close_const_prob + same_const_prob:
            res = random.choice(consts_generated) + random.choice((-EPS, EPS))
        else:
            res = random.uniform(-10.0, 10.0)

        res = round(res, DIGITS)
        if res not in consts_generated:
            consts_generated.append(res)
        return res

    poly_type: str
    if max_depth == 0:
        if no_exp:
            poly_type = "mono"
        else:
            poly_type = random.choice(("mono", "exp"))
    else:
        if no_exp:
            poly_type = random.choices(
                ("mono", "scl", "add", "sub", "mul"),
                weights=(1, 2, 3, 3, 3),
            )[0]
        else:
            poly_type = random.choices(
                ("mono", "exp", "scl", "add", "sub", "mul"),
                weights=(1, 1, 2, 3, 3, 3),
            )[0]

    c: float
    left: tuple[Expr, list[float]]
    right: tuple[Expr, list[float]]
    if poly_type == "mono":
        return (Mono(generate_constant()), consts_generated)
    if poly_type == "exp":
        return (Exp(), consts_generated)
    if poly_type == "scl":
        c = generate_constant()
        left = generate_poly(
            max_depth - 1, no_exp, same_const_prob, close_const_prob, consts_generated
        )
        return (Scl(c, left[0]), left[1])
    if poly_type == "add":
        left = generate_poly(
            max_depth - 1, no_exp, same_const_prob, close_const_prob, consts_generated
        )
        right = generate_poly(
            max_depth - 1, no_exp, same_const_prob, close_const_prob, left[1]
        )
        return (Add(left[0], right[0]), right[1])
    if poly_type == "sub":
        left = generate_poly(
            max_depth - 1, no_exp, same_const_prob, close_const_prob, consts_generated
        )
        right = generate_poly(
            max_depth - 1, no_exp, same_const_prob, close_const_prob, left[1]
        )
        return (Sub(left[0], right[0]), right[1])
    if poly_type == "mul":
        left = generate_poly(
            max_depth - 1, no_exp, same_const_prob, close_const_prob, consts_generated
        )
        right = generate_poly(
            max_depth - 1, no_exp, same_const_prob, close_const_prob, left[1]
        )
        return (Mul(left[0], right[0]), right[1])
    raise ValueError("This should never happen.")


def fuzz(
    n: int,
    max_depth: int,
    verbose: bool = False,
    no_top: bool = False,
    no_exp: bool = False,
    min_size: int = -1,
    same_const_prob: float = 0.2,
    close_const_prob: float = 0.2,
) -> None:
    """Fuzz the polynomial expansion and asymptotic analysis."""
    tot: int = 0
    tight: int = 0
    loose: int = 0
    incorrect: int = 0

    while tot < n:
        p: Expr = generate_poly(max_depth, no_exp, same_const_prob, close_const_prob)[0]
        if min_size > 0 and p.size() < min_size:
            continue
        a: Asymptotic = asymptotic(p)
        if no_top and a == "top":
            continue
        tot += 1

        expanded: PolyExpanded = PolyExpanded.from_poly(p)
        lead: tuple[TermPower, float] = expanded.leading_term()
        test: AsymptoticTest = test_asymptotic(lead, a)

        if test == "Tight":
            tight += 1
        elif test == "Loose":
            loose += 1
        else:  # test == "Incorrect"
            incorrect += 1

        if verbose or test != "Tight":
            print(f"Test {tot}: {test} for {p}")
            print(f"{lead[1]} * {lead[0]} {'>' if test == 'Incorrect' else '<='} {a}")
        if tot < n and tot % 10 == 0:
            print()
            print(f"Progress: {tot} trials, ")
            print(f"{tight} tight, {loose} loose, {incorrect} incorrect.")
            print()

    print()
    print(f"Finished {tot} trials.")
    print(f"Tight: {tight}, Loose: {loose}, Incorrect: {incorrect}.")


if __name__ == "__main__":
    random.seed(314159)
    fuzz(3000, 10, no_top=True, min_size=4)
