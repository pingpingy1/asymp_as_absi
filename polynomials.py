"""Definition of polynomials of real coefficients and expoenents."""

EPS: float = 1e-6


def equals(x: float, y: float) -> bool:
    """Check if two floats are equal."""
    return abs(x - y) < EPS


class IntFunc:
    """General class for integer functions."""

    atomic: bool = False

    def eval(self, n: int) -> float:
        """Evaluate the function at x."""
        raise NotImplementedError("Subclasses must implement this method.")

    def str_as_sub(self) -> str:
        """Return the string representation of the function as a subscript."""
        if self.atomic:
            return str(self)
        return f"({self})"


class Mono(IntFunc):
    atomic: bool = True

    def __init__(self, r: float) -> None:
        self.r: float = r

    def eval(self, n: int) -> float:
        if equals(self.r, 0.0):
            return 1.0
        return float(n**self.r)

    def __str__(self) -> str:
        return f"n^({self.r})"


class Exp(IntFunc):
    atomic: bool = True

    def __init__(self) -> None:
        pass

    def eval(self, n: int) -> float:
        return float(2**n)

    def __str__(self) -> str:
        return "2^n"


class Scl(IntFunc):
    atomic: bool = True

    def __init__(self, c: float, f: IntFunc) -> None:
        self.c: float = c
        self.f: IntFunc = f

    def eval(self, n: int) -> float:
        if equals(self.c, 0.0):
            return 0
        return self.c * self.f.eval(n)

    def __str__(self) -> str:
        return f"{self.c} {self.f.str_as_sub()}"


class Add(IntFunc):
    atomic: bool = False

    def __init__(self, l: IntFunc, r: IntFunc) -> None:
        self.l: IntFunc = l
        self.r: IntFunc = r

    def eval(self, n: int) -> float:
        return self.l.eval(n) + self.r.eval(n)

    def __str__(self) -> str:
        return f"{self.l.str_as_sub()} + {self.r.str_as_sub()}"


class Sub(IntFunc):
    atomic: bool = False

    def __init__(self, l: IntFunc, r: IntFunc) -> None:
        self.l: IntFunc = l
        self.r: IntFunc = r

    def eval(self, n: int) -> float:
        return self.l.eval(n) - self.r.eval(n)

    def __str__(self) -> str:
        return f"{self.l.str_as_sub()} - {self.r.str_as_sub()}"


class Mul(IntFunc):
    atomic: bool = False

    def __init__(self, l: IntFunc, r: IntFunc):
        self.l: IntFunc = l
        self.r: IntFunc = r

    def eval(self, n: int) -> float:
        return self.l.eval(n) * self.r.eval(n)

    def __str__(self) -> str:
        return f"{self.l.str_as_sub()} * {self.r.str_as_sub()}"


def test() -> None:
    """Test the evaluation of (n^1.0 + 2.0 n^0.0) * (0.5 n^3.0 - n^2.0) for n = 0, 1, ..., 9."""
    f_imp: IntFunc = Mul(
        Add(Mono(1.0), Scl(2.0, Mono(0.0))), Sub(Scl(0.5, Mono(3.0)), Mono(2.0))
    )

    def f_ans(n: int) -> float:
        return float((n**1.0 + 2.0 * n**0.0) * (0.5 * n**3.0 - n**2.0))

    print(f"Function: {f_imp}")

    for n in range(10):
        impl: float = f_imp.eval(n)
        ans: float = f_ans(n)
        assert equals(impl, ans), f"Failed: {n} -> {impl} != {ans}"
        print(f"Passed: {n} -> {impl}")


if __name__ == "__main__":
    test()
