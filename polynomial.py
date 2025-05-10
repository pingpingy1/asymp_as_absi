"""Definition of polynomials of real coefficients and exponents."""

EPS: float = 1e-6


def equals(x: float, y: float) -> bool:
    """Check if two floats are equal."""
    return abs(x - y) < EPS


class Polynomial:
    """General class for integer polynomials."""

    atomic: bool = False

    def eval(self, _: int) -> float:
        """Evaluate the function at x."""
        raise NotImplementedError("Subclasses must implement this method.")

    def str_as_sub(self) -> str:
        """Return the string representation of the function as a subscript."""
        if self.atomic:
            return str(self)
        return f"({self})"

    def size(self) -> int:
        """Return the size of the polynomial."""
        raise NotImplementedError("Subclasses must implement this method.")


class Mono(Polynomial):
    """n^r for some real r."""

    atomic: bool = True

    def __init__(self, r: float) -> None:
        self.r: float = r

    def eval(self, n: int) -> float:
        if equals(self.r, 0.0):
            return 1.0
        return float(n**self.r)

    def __str__(self) -> str:
        return f"n^({self.r})"

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}({self.r})"

    def size(self) -> int:
        return 1


class Exp(Polynomial):
    """2^n."""

    atomic: bool = True

    def __init__(self) -> None:
        pass

    def eval(self, n: int) -> float:
        return float(2**n)

    def __str__(self) -> str:
        return "2^n"

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}()"

    def size(self) -> int:
        return 1


class Scl(Polynomial):
    """cf(n) for some real c."""

    atomic: bool = True

    def __init__(self, c: float, f: Polynomial) -> None:
        self.c: float = c
        self.f: Polynomial = f

    def eval(self, n: int) -> float:
        if equals(self.c, 0.0):
            return 0
        return self.c * self.f.eval(n)

    def __str__(self) -> str:
        return f"{self.c} {self.f.str_as_sub()}"

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}({self.c}, {repr(self.f)})"

    def size(self) -> int:
        return 1 + self.f.size()


class Add(Polynomial):
    """f(n) + g(n)."""

    atomic: bool = False

    def __init__(self, l: Polynomial, r: Polynomial) -> None:
        self.l: Polynomial = l
        self.r: Polynomial = r

    def eval(self, n: int) -> float:
        return self.l.eval(n) + self.r.eval(n)

    def __str__(self) -> str:
        return f"{self.l.str_as_sub()} + {self.r.str_as_sub()}"

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}({repr(self.l)}, {repr(self.r)})"

    def size(self) -> int:
        return 1 + self.l.size() + self.r.size()


class Sub(Polynomial):
    """f(n) - g(n)."""

    atomic: bool = False

    def __init__(self, l: Polynomial, r: Polynomial) -> None:
        self.l: Polynomial = l
        self.r: Polynomial = r

    def eval(self, n: int) -> float:
        return self.l.eval(n) - self.r.eval(n)

    def __str__(self) -> str:
        return f"{self.l.str_as_sub()} - {self.r.str_as_sub()}"

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}({repr(self.l)}, {repr(self.r)})"

    def size(self) -> int:
        return 1 + self.l.size() + self.r.size()


class Mul(Polynomial):
    """f(n) * g(n)."""

    atomic: bool = False

    def __init__(self, l: Polynomial, r: Polynomial):
        self.l: Polynomial = l
        self.r: Polynomial = r

    def eval(self, n: int) -> float:
        return self.l.eval(n) * self.r.eval(n)

    def __str__(self) -> str:
        return f"{self.l.str_as_sub()} * {self.r.str_as_sub()}"

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}({repr(self.l)}, {repr(self.r)})"

    def size(self) -> int:
        return 1 + self.l.size() + self.r.size()
