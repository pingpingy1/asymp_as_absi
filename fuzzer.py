"""Fuzzer to compare the full expansion and the asymptotic analysis."""

import random
import time
from polynomial import equals, Polynomial, Mono, Exp, Scl, Add, Sub, Mul
from poly_expanded import TermPower, PolyExpanded
from asymptotic import asymptotic, Asymptotic


def correct(expanded: list[tuple[TermPower, float]], asymp: Asymptotic) -> bool:
    """Check if the asymptotic analysis yields a sound approximation of the expanded polynomial."""
    if asymp == "top":
        return True
    if asymp == "bottom":
        return len(expanded) == 0

    exp_t, exp_c = expanded[-1]
    asymp_c, asymp_r = asymp

    if exp_t.exp_power > 0:
        return False
    if equals(exp_t.deg_power, asymp_r):
        return equals(abs(exp_c), abs(asymp_c)) or abs(exp_c) < abs(asymp_c)
    return exp_t.deg_power < asymp_r


def generate_poly(max_depth: int) -> Polynomial:
    """Generate a random polynomial with a maximum depth of `max_depth`."""
    poly_type: str
    if max_depth == 0:
        poly_type = random.choice(("mono", "exp"))
    else:
        poly_type = random.choice(
            (
                "mono",
                "mono",
                "exp",
                "scl",
                "add",
                "add",
                "add",
                "add",
                "sub",
                "sub",
                "sub",
                "sub",
                "mul",
                "mul",
                "mul",
                "mul",
            )
        )

    if poly_type == "mono":
        return Mono(random.uniform(-10.0, 10.0))
    if poly_type == "exp":
        return Exp()
    if poly_type == "scl":
        return Scl(random.uniform(-10.0, 10.0), generate_poly(max_depth - 1))
    if poly_type == "add":
        return Add(
            generate_poly(max_depth - 1),
            generate_poly(max_depth - 1),
        )
    if poly_type == "sub":
        return Sub(
            generate_poly(max_depth - 1),
            generate_poly(max_depth - 1),
        )
    if poly_type == "mul":
        return Mul(
            generate_poly(max_depth - 1),
            generate_poly(max_depth - 1),
        )
    raise ValueError("This should never happen.")


def fuzz(n: int, max_depth: int, verbose: bool = False) -> None:
    """Fuzz the polynomial expansion and asymptotic analysis."""
    tot: int = 0
    asymp_time: float = 0.0
    expanded_time: float = 0.0

    while tot < n:
        p: Polynomial = generate_poly(max_depth)

        asymp_start: float = time.perf_counter()
        a = asymptotic(p)
        asymp_end: float = time.perf_counter()

        if a == "top" or p.size() < 4:
            continue
        asymp_time += asymp_end - asymp_start
        tot += 1

        expanded_start: float = time.perf_counter()
        expanded: PolyExpanded = PolyExpanded.from_poly(p)
        expanded_end: float = time.perf_counter()
        expanded_time += expanded_end - expanded_start

        assert correct(expanded.coeff(), a), f"p = {p} -> {expanded} > {a}"
        if verbose:
            print(f"p = {p} -> {expanded} <= {a}")
        if tot % 10 == 0:
            print(
                f"{tot} trials..."
                + (
                    f" ({expanded_time * 1000:.5f}ms, {asymp_time * 1000:.5f}ms)"
                    if verbose
                    else ""
                )
            )

    print(f"Finished {tot} trials.")
    print(
        f"Expanded time: {expanded_time * 1000:.5f}ms, Asymptotic time: {asymp_time * 1000:.5f}ms"
    )


if __name__ == "__main__":
    random.seed(314159)
    fuzz(30, 10, verbose=True)
