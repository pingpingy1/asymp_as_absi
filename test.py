"""Unit tests for the polynomial representations."""

import unittest
from typing import Callable
from polynomial import EPS, Polynomial, Mono, Exp, Scl, Add, Sub, Mul
from asymptotic import asymptotic, Asymptotic, asymptotic_eq
from poly_expanded import PolyExpanded


class TestPolynomial(unittest.TestCase):
    """Unit tests for the polynomial representations."""

    def assert_func_equivalent(
        self,
        f: Callable[[int], float],
        g: Callable[[int], float],
    ) -> None:
        """Assert that two functions are nearly equivalent for n in [1, 10]."""
        for n in range(1, 11):
            f_eval: float = f(n)
            g_eval: float = g(n)
            self.assertAlmostEqual(f_eval, g_eval, delta=EPS)

    def assert_asymp_equal(
        self,
        a1: Asymptotic,
        a2: Asymptotic,
    ) -> None:
        """Assert that two asymptotic analyses are equivalent."""
        self.assertTrue(asymptotic_eq(a1, a2), f"asymptotic({a1}) != asymptotic({a2})")

    def setUp(self) -> None:
        # Polynomial 1:
        # (3n^1.2 + 2^n)*(5n^0.8 - 1) - n^2 - 2^n
        # = -3n^1.2 + 14n^2 + 5n^0.8 2^n
        self.poly1: Polynomial = Add(
            Sub(
                Mul(
                    Add(
                        Scl(3.0, Mono(1.2)),
                        Exp(),
                    ),
                    Sub(
                        Scl(5.0, Mono(0.8)),
                        Mono(0.0),
                    ),
                ),
                Mono(2.0),
            ),
            Exp(),
        )
        self.poly1_ans: Callable[[int], float] = lambda n: float(
            -3.0 * n**1.2 + 14.0 * n**2.0 + 5.0 * n**0.8 * 2.0**n
        )

        # Polynomial 2:
        # 0.0*(2^n + 3.5n^0.7) + (1.7n^4 + 0.2n^1.7)*(3.5n^0.8 - 1.1n^(-0.2))
        # = -0.22n^1.5 + 0.7n^2.5 - 1.87n^3.8 + 5.95n^4.8
        self.poly2: Polynomial = Add(
            Scl(0.0, Add(Exp(), Scl(3.5, Mono(0.7)))),
            Mul(
                Add(
                    Scl(1.7, Mono(4.0)),
                    Scl(0.2, Mono(1.7)),
                ),
                Sub(
                    Scl(3.5, Mono(0.8)),
                    Scl(1.1, Mono(-0.2)),
                ),
            ),
        )
        self.poly2_ans: Callable[[int], float] = lambda n: float(
            -0.22 * n**1.5 + 0.7 * n**2.5 - 1.87 * n**3.8 + 5.95 * n**4.8
        )

    def test_poly(self) -> None:
        """Test the polynomial representations."""
        self.assert_func_equivalent(self.poly1.eval, self.poly1_ans)
        self.assert_func_equivalent(self.poly2.eval, self.poly2_ans)

    def test_asymptotic(self) -> None:
        """Test the asymptotic analysis of the polynomials."""
        self.assert_asymp_equal(asymptotic(self.poly1), "top")
        self.assert_asymp_equal(asymptotic(self.poly2), (5.95, 4.8))

    def test_expanded(self) -> None:
        """Test the expanded polynomial representation."""
        self.assert_func_equivalent(
            PolyExpanded.from_poly(self.poly1).eval, self.poly1_ans
        )
        self.assert_func_equivalent(
            PolyExpanded.from_poly(self.poly2).eval, self.poly2_ans
        )


if __name__ == "__main__":
    unittest.main(verbosity=2)
