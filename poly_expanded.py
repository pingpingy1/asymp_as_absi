"""Expanded representation of polynomials"""

from math import inf
from expr import Expr, Mono, Exp, Scl, Add, Sub, Mul, equals


class TermPower:
    """The power of a term. 2^(exp_power*n) * n^deg_power."""

    def __init__(self, exp_power: int, deg_power: float) -> None:
        self.powers: tuple[int, float] = (exp_power, deg_power)
        self.__validate()

    def __validate(self) -> None:
        assert self.powers[0] >= 0, f"exp_power must be non-negative: {self.powers[0]}"

    @property
    def exp_power(self) -> int:
        """The exponent power of the term."""
        return self.powers[0]

    @property
    def deg_power(self) -> float:
        """The degree power of the term."""
        return self.powers[1]

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, TermPower):
            return False
        return self.exp_power == other.exp_power and equals(
            self.deg_power, other.deg_power
        )

    def __lt__(self, other: object) -> bool:
        if not isinstance(other, TermPower):
            return NotImplemented
        return self != other and self.powers < other.powers

    def __le__(self, other: object) -> bool:
        if not isinstance(other, TermPower):
            return NotImplemented
        return self == other or self.powers < other.powers

    def __str__(self) -> str:
        return f"2^({self.exp_power}n) * n^({self.deg_power})"

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}{self.powers}"


ZERO_LEADING: tuple[TermPower, float] = (TermPower(0, -inf), 0.0)


class PolyExpanded:
    """Expanded representation of polynomials."""

    __coeff: list[tuple[TermPower, float]]

    def __new__(cls, coeff: list[tuple[TermPower, float]]) -> "PolyExpanded":
        """Create a polynomial from a list of coefficients."""
        return cls.__create_inst_without_sort(coeff, need_sort=True)

    @classmethod
    def __create_inst_without_sort(
        cls, coeff: list[tuple[TermPower, float]], need_sort: bool
    ) -> "PolyExpanded":
        """Used internally to create an instance when `coeff` is guaranteed to be sorted."""
        self: "PolyExpanded" = super().__new__(cls)
        self.__coeff = coeff.copy()
        self.__validate(need_sort)
        return self

    def __validate(self, need_sort: bool) -> None:
        # 1. Remove zero coefficients
        self.__coeff = list(filter(lambda x: not equals(x[1], 0.0), self.__coeff))

        # 2. Sort by increasing order of powers
        if need_sort:
            self.__coeff.sort()

        # 3. Check for duplicates
        i: int = 0
        while i < len(self.__coeff) - 1:
            while (
                i < len(self.__coeff) - 1
                and self.__coeff[i][0] == self.__coeff[i + 1][0]
            ):
                self.__coeff[i] = (
                    self.__coeff[i][0],
                    self.__coeff[i][1] + self.__coeff[i + 1][1],
                )
                del self.__coeff[i + 1]
            i += 1

    def coeff(self) -> list[tuple[TermPower, float]]:
        """Get a copy of the coefficients of the polynomial."""
        return self.__coeff.copy()

    def scl(self, r: float) -> "PolyExpanded":
        """Multiply the polynomial by a scalar."""
        return PolyExpanded([(t, c * r) for t, c in self.__coeff])

    def __neg__(self) -> "PolyExpanded":
        return PolyExpanded([(t, -c) for t, c in self.__coeff])

    def __add__(self, other: object) -> "PolyExpanded":
        if not isinstance(other, PolyExpanded):
            return NotImplemented
        res: list[tuple[TermPower, float]] = other.coeff()
        i: int = 0 # index for res
        j: int = 0 # index for self.__coeff
        while j < len(self.__coeff):
            while i < len(res) and res[i][0] < self.__coeff[j][0]:
                i += 1
            if i >= len(res):
                res.extend(self.__coeff[j:])
                j = len(self.__coeff)
                break

            if res[i][0] == self.__coeff[j][0]:
                res[i] = (res[i][0], res[i][1] + self.__coeff[j][1])
            else:
                res.insert(i, self.__coeff[j])
            j += 1
        return self.__create_inst_without_sort(res, False)

    def __sub__(self, other: object) -> "PolyExpanded":
        if not isinstance(other, PolyExpanded):
            return NotImplemented
        res: list[tuple[TermPower, float]] = [
            (t, -c) for t, c in other.coeff()
        ]
        i: int = 0 # index for res
        j: int = 0 # index for self.__coeff
        while j < len(self.__coeff):
            while i < len(res) and res[i][0] < self.__coeff[j][0]:
                i += 1
            if i >= len(res):
                res.extend(self.__coeff[j:])
                j = len(self.__coeff)
                break

            if res[i][0] == self.__coeff[j][0]:
                res[i] = (res[i][0], res[i][1] + self.__coeff[j][1])
            else:
                res.insert(i, self.__coeff[j])
            j += 1
        return self.__create_inst_without_sort(res, False)

    def __mul__(self, other: object) -> "PolyExpanded":
        if not isinstance(other, PolyExpanded):
            return NotImplemented
        res: list[tuple[TermPower, float]] = []
        for t1, c1 in self.__coeff:
            for t2, c2 in other.coeff():
                new_term: tuple[TermPower, float] = (
                    TermPower(t1.exp_power + t2.exp_power, t1.deg_power + t2.deg_power),
                    c1 * c2,
                )
                i: int = self.bin_search(res, new_term[0])
                if i < len(res) and res[i][0] == new_term[0]:
                    res[i] = (res[i][0], res[i][1] + new_term[1])
                else:
                    res.insert(i, new_term)
        return self.__create_inst_without_sort(res, False)

    @classmethod
    def bin_search(cls, coeff: list[tuple[TermPower, float]], t: TermPower) -> int:
        """Binary search for the index of the term in the coefficients."""
        low: int = 0
        high: int = len(coeff) - 1
        while low <= high:
            mid: int = (low + high) // 2
            if coeff[mid][0] == t:
                return mid
            if coeff[mid][0] < t:
                low = mid + 1
            else:
                high = mid - 1
        return low

    @classmethod
    def from_poly(cls, poly: Expr) -> "PolyExpanded":
        """Create a PolyExpanded from an Expr."""
        if isinstance(poly, Mono):
            return cls([(TermPower(0, poly.r), 1.0)])
        if isinstance(poly, Exp):
            return cls([(TermPower(1, 0.0), 1.0)])
        if isinstance(poly, Scl):
            return PolyExpanded.from_poly(poly.f).scl(poly.c)
        if isinstance(poly, Add):
            return PolyExpanded.from_poly(poly.l) + PolyExpanded.from_poly(poly.r)
        if isinstance(poly, Sub):
            return PolyExpanded.from_poly(poly.l) - PolyExpanded.from_poly(poly.r)
        if isinstance(poly, Mul):
            return PolyExpanded.from_poly(poly.l) * PolyExpanded.from_poly(poly.r)
        raise NotImplementedError(f"Unsupported polynomial type: {type(poly)}")

    def __str__(self) -> str:
        return " + ".join(
            (
                f"({c})"
                + ("" if equals(t.deg_power, 0.0) else f"n^({t.deg_power})")
                + ("" if equals(t.exp_power, 0.0) else f"2^({t.exp_power}n)")
            )
            for t, c in self.__coeff
        )

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}({self.__coeff})"

    def eval(self, n: int) -> float:
        """Evaluate the polynomial at n."""
        return sum(
            float(c * (2 ** (t.exp_power * n)) * (n**t.deg_power)) for t, c in self.__coeff
        )

    def leading_term(self) -> tuple[TermPower, float]:
        """Get the leading term of the polynomial."""
        if not self.__coeff:
            return ZERO_LEADING
        return self.__coeff[-1]

    @classmethod
    def coeff_to_str(cls, coeff: list[tuple[TermPower, float]]) -> str:
        """Convert the coefficients to a string."""
        return "[" + ", ".join(f"({t}, {c})" for t, c in coeff) + "]"
