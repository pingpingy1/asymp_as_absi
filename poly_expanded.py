"""Expanded representation of polynomials"""

from polynomials import IntFunc, Mono, Exp, Scl, Add, Sub, Mul, equals

type Degree = tuple[int, float]  # degree of the polynomial
type Coeffs = list[tuple[Degree, float]]  # coefficients of the polynomial


def degrees_equal(d1: Degree, d2: Degree) -> bool:
    """Check if two degrees are equal."""
    return d1[0] == d2[0] and equals(d1[1], d2[1])


def degrees_less(d1: Degree, d2: Degree) -> bool:
    """Check if degree d1 is less than degree d2."""
    if d1[0] == d2[0]:
        return d1[1] < d2[1]
    return d1[0] < d2[0]


def add_coeffs(cs1: Coeffs, cs2: Coeffs) -> Coeffs:
    """Add two lists of coefficients. Assumes the two are sorted."""
    result: Coeffs = []
    i, j = 0, 0
    while i < len(cs1) and j < len(cs2):
        if degrees_equal(cs1[i][0], cs2[j][0]):
            result.append((cs1[i][0], cs1[i][1] + cs2[j][1]))
            i += 1
            j += 1
        elif cs1[i][0] < cs2[j][0]:
            result.append(cs1[i])
            i += 1
        else:
            result.append(cs2[j])
            j += 1
    if i < len(cs1):
        result.extend(cs1[i:])
    elif j < len(cs2):
        result.extend(cs2[j:])

    # Result is guaranteed to be sorted
    # Remove zero coefficients
    return [c for c in result if not equals(c[1], 0.0)]


def mul_coeffs(cs1: Coeffs, cs2: Coeffs) -> Coeffs:
    """Multiply two lists of coefficients. Assumes the two are sorted."""

    def find_index(result: Coeffs, deg: Degree) -> int:
        """Binary search to find insertion index for key in sorted result."""
        low, high = 0, len(result)
        while low < high:
            mid = (low + high) // 2
            if degrees_less(result[mid][0], deg):
                low = mid + 1
            else:
                high = mid
        return low

    result: Coeffs = []
    for d1, a1 in cs1:
        for d2, a2 in cs2:
            d: Degree = (d1[0] + d2[0], d1[1] + d2[1])
            c: float = a1 * a2

            if equals(c, 0.0):
                continue

            idx: int = find_index(result, d)

            if idx < len(result) and degrees_equal(result[idx][0], d):
                new_c: float = result[idx][1] + c
                if equals(new_c, 0.0):
                    result.pop(idx)
                else:
                    result[idx] = (d, new_c)
            else:
                result.insert(idx, (d, c))
    return result


def expand(poly: IntFunc) -> Coeffs:
    """Expand the polynomial `poly` into a list of coefficients."""
    if isinstance(poly, Mono):
        return [((0, poly.r), 1.0)]

    if isinstance(poly, Exp):
        return [((0, 1.0), 1.0)]

    if isinstance(poly, Scl):
        if equals(poly.c, 0.0):
            return []
        coeffs = expand(poly.f)
        return [(c[0], c[1] * poly.c) for c in coeffs]

    if isinstance(poly, (Add, Sub)):
        l_coeffs = expand(poly.l)
        r_coeffs = expand(poly.r)
        if isinstance(poly, Sub):
            r_coeffs = [(c[0], -c[1]) for c in r_coeffs]
        return add_coeffs(l_coeffs, r_coeffs)

    if isinstance(poly, Mul):
        l_coeffs = expand(poly.l)
        r_coeffs = expand(poly.r)
        return mul_coeffs(l_coeffs, r_coeffs)

    raise ValueError(f"Unknown polynomial type: {type(poly)}")


def eval_poly(coeffs: Coeffs, n: int) -> float:
    """Evaluate the polynomial represented by `coeffs` at `n`."""
    result: float = 0.0
    for d, a in coeffs:
        result += a * (2 ** (d[0] * n)) * (n ** d[1])
    return result


def test() -> None:
    """Test the evaluation of (n^1.0 + 2.0 n^0.0) * (0.5 n^3.0 - n^2.0) for n = 0, 1, ..., 9."""
    f_imp: IntFunc = Mul(
        Add(Mono(1.0), Scl(2.0, Mono(0.0))), Sub(Scl(0.5, Mono(3.0)), Mono(2.0))
    )
    coeffs: Coeffs = expand(f_imp)  # Ans: [((0, 2.0), 2.0), ((0, 4.0), 0.5)]
    print(f"Expanded coefficients: {coeffs}")
    for n in range(10):
        impl: float = eval_poly(coeffs, n)
        ans: float = f_imp.eval(n)
        assert equals(impl, ans), f"Failed: {n} -> {impl} != {ans}"
        print(f"Passed: {n} -> {impl} == {ans}")


if __name__ == "__main__":
    test()
