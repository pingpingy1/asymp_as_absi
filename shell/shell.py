"""Simple interactive shell for evaluating and analyzing function expressions."""

import argparse
from expr import Expr
from poly_expanded import TermPower, PolyExpanded
from asymptotic import asymptotic, Asymptotic
from parse import parse
from fuzzer import test_asymptotic, fuzz


def shell_help() -> None:
    """Prints the help message for the shell."""
    print("Simple shell for evaluating function expressions.")
    print("Commands:")
    print("  help                           - Show this help message")
    print("  exit                           - Exit the shell")
    print(
        "  eval <expr> at <n>             - Evaluate the expression at the given value"
    )
    print("  analyze <expr>                 - Analyze the expression")
    print("  fuzz <n> <max_depth> [options] - Run fuzzer on the asymptotic analysis")
    print("    n                            - Number of trials to run")
    print("    max_depth                    - Maximum depth of the expression tree")
    print("    -v, --verbose                - Print all trials")
    print(
        "    --no-top                     - Ignore test cases if analysis results in top"
    )
    print("    --no-exp                     - Do not allow exponential terms")
    print(
        "    --min-size <size>            - Minimum size of the expression to consider"
    )
    print("    --same-const-prob <p>        - Probability of reusing a constant")
    print("    --close-const-prob <p>       - Probability of perturbating a constant")
    print()
    print("Expression syntax:")
    print("  <expr> ::= n                   (Identity)")
    print("           | <float>             (Constant)")
    print("           | n^<float>           (Monomial)")
    print("           | 2^n                 (Exponential)")
    print("           | <float> * <expr>    (Constant Scaling)")
    print("           | <expr> + <expr>     (Sum)")
    print("           | <expr> - <expr>     (Difference)")
    print("           | <expr> * <expr>     (Product)")
    print("           | (<expr>)            (Parentheses)")


def shell() -> None:
    """Interactive shell for evaluating and analyzing function expressions."""
    fuzzer_parser: argparse.ArgumentParser = argparse.ArgumentParser()
    fuzzer_parser.add_argument("n", type=int, help="Number of trials to run")
    fuzzer_parser.add_argument(
        "max_depth", type=int, help="Maximum depth of the expression tree"
    )
    fuzzer_parser.add_argument(
        "-v",
        "--verbose",
        action="store_true",
        help="Print all trials",
    )
    fuzzer_parser.add_argument(
        "--no-top",
        action="store_true",
        help="Ignore test cases if analysis results in top",
    )
    fuzzer_parser.add_argument(
        "--no-exp",
        action="store_true",
        help="Do not allow exponential terms",
    )
    fuzzer_parser.add_argument(
        "--min-size",
        type=int,
        default=-1,
        help="Minimum size of the expression to consider",
    )
    fuzzer_parser.add_argument(
        "--same-const-prob",
        type=float,
        default=0.2,
        help="Probability of reusing a constant",
    )
    fuzzer_parser.add_argument(
        "--close-const-prob",
        type=float,
        default=0.2,
        help="Probability of perturbating a constant",
    )
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
        elif cmd.startswith("fuzz"):
            try:
                args = fuzzer_parser.parse_args(cmd[4:].strip().split())
                fuzz(
                    args.n,
                    args.max_depth,
                    verbose=args.verbose,
                    no_top=args.no_top,
                    no_exp=args.no_exp,
                    min_size=args.min_size,
                    same_const_prob=args.same_const_prob,
                    close_const_prob=args.close_const_prob,
                )
            except SystemExit:
                # argparse will exit the program if there is an error
                continue
        else:
            print(f"Unknown command: {cmd}")


if __name__ == "__main__":
    shell()
