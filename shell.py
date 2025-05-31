"""Simple interactive shell for evaluating and analyzing function expressions."""

from expr import Expr
from poly_expanded import TermPower, PolyExpanded
from asymptotic import asymptotic, Asymptotic
from parse import parse
from fuzzer import test_asymptotic


def shell_help() -> None:
    """Prints the help message for the shell."""
    print("Simple shell for evaluating function expressions.")
    print("Commands:")
    print("  help                 - Show this help message")
    print("  exit                 - Exit the shell")
    print("  eval <expr> at <int> - Evaluate the expression at the given value")
    print("  analyze <expr>       - Analyze the expression (not implemented yet)")
    print()
    print("Syntax:")
    print("  <expr> ::= n                (Identity)")
    print("           | <float>          (Constant)")
    print("           | n^<float>        (Monomial)")
    print("           | 2^n              (Exponential)")
    print("           | <float> * <expr> (Constant Scaling)")
    print("           | <expr> + <expr>  (Sum)")
    print("           | <expr> - <expr>  (Difference)")
    print("           | <expr> * <expr>  (Product)")
    print("           | (<expr>)         (Parentheses)")


def shell() -> None:
    """Interactive shell for evaluating and analyzing function expressions."""
    while True:
        cmd: str = input(">>> ")
        expr_str: str
        expr: Expr

        if cmd.startswith("exit"):
            break

        if cmd.startswith("help"):
            shell_help()
        elif cmd.startswith("eval"):
            idx: int = cmd.rfind("at")
            if idx < 0:
                print("Error: 'eval' command without 'at'")
            else:
                expr_str = cmd[4:idx].strip()
                at: str = cmd[idx + 2 :].strip()
                try:
                    expr = parse(expr_str)
                    print(f"({expr})({at}) = {expr.eval(int(at))}")
                except ValueError as e:
                    print(f"{e}")
        elif cmd.startswith("analyze"):
            expr_str = cmd[7:].strip()
            try:
                expr = parse(expr_str)
                print(f"AST: {repr(expr)}")

                expanded: PolyExpanded = PolyExpanded.from_poly(expr)
                print(f"Expanded: {expanded}")

                lead: tuple[TermPower, float] = expanded.leading_term()
                print(f"Leading term: {lead[1]} * {lead[0]}")

                asymp: Asymptotic = asymptotic(expr)
                print(f"Asymptotic: {asymp}")
                print(f"Analysis: {test_asymptotic(lead, asymp)}")
            except ValueError as e:
                print(f"{e}")
        else:
            print(f"Unknown command: {cmd}")


if __name__ == "__main__":
    shell()
