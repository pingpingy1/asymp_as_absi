"""Parser for function expressions."""
from expr import Expr, Mono, Exp, Scl, Add, Sub, Mul

TT_VAR: str = "TT_VAR"
TT_NUM: str = "TT_NUM"
TT_OP: str = "TT_OP"
TT_LPAREN: str = "TT_LPAREN"
TT_RPAREN: str = "TT_RPAREN"

NUMERIC: str = "0123456789."
OPS: str = "+-*^"


class Lexer:
    """Tokenizes the input expression string."""

    def __init__(self, expr: str) -> None:
        self.expr: str = expr.strip()
        self.pos: int = -1
        self.curr: str | None = None
        self.tokens: list[tuple[str, str, int]] = []
        self.advance()

    def advance(self) -> None:
        """Advances to the next character in the expression."""
        if self.pos < len(self.expr) - 1:
            self.pos += 1
            self.curr = self.expr[self.pos]
        else:
            self.curr = None

    def next_token(self) -> tuple[str, str, int]:
        """Returns the next token. Raises ValueError if no more tokens are available."""
        if not self.curr:
            raise ValueError(f"Unexpected eof at {self.pos}")
        while self.curr.isspace():
            self.advance()
            if not self.curr:
                raise ValueError(f"Unexpected eof at {self.pos}")

        tok_pos: int = self.pos
        if self.curr == "n":
            self.advance()
            return (TT_VAR, "n", tok_pos)

        if self.curr in NUMERIC:
            const_str: str = ""
            while self.curr and self.curr in NUMERIC:
                const_str += self.curr
                self.advance()
            return (TT_NUM, const_str, tok_pos)

        if self.curr in OPS:
            op_str: str = self.curr
            self.advance()
            return (TT_OP, op_str, tok_pos)

        if self.curr == "(":
            self.advance()
            return (TT_LPAREN, "(", tok_pos)

        if self.curr == ")":
            self.advance()
            return (TT_RPAREN, ")", tok_pos)

        raise ValueError(f"Unexpected character at {self.pos}: {self.curr}")

    def tokenize(self) -> list[tuple[str, str, int]]:
        """Tokenizes the entire expression."""
        while self.curr:
            self.tokens.append(self.next_token())
        return self.tokens


class Parser:
    """Parses the tokenized expression into an Expr tree."""

    def __init__(self, tokens: list[tuple[str, str, int]]) -> None:
        self.tokens: list[tuple[str, str, int]] = tokens
        self.pos: int = -1
        self.curr: tuple[str, str, int] | None = None
        self.advance()

    def advance(self) -> None:
        """Advances to the next token."""
        if self.pos < len(self.tokens) - 1:
            self.pos += 1
            self.curr = self.tokens[self.pos]
        else:
            self.curr = None

    def parse_expr(self) -> Expr:
        """Parses an expression."""
        left: Expr = self.parse_term()
        return self.parse_expr_tail(left)

    def parse_expr_tail(self, left: Expr) -> Expr:
        """Parses the rest of the expression after a term."""
        if not self.curr:
            return left
        if self.curr[0] == TT_OP and self.curr[1] in "+-":
            op: str = self.curr[1]
            self.advance()
            right: Expr = self.parse_term()
            if op == "+":
                return self.parse_expr_tail(Add(left, right))
            elif op == "-":
                return self.parse_expr_tail(Sub(left, right))
        return left

    def parse_term(self) -> Expr:
        """Parses a term."""
        left: Expr = self.parse_factor()
        return self.parse_term_tail(left)

    def parse_term_tail(self, left: Expr) -> Expr:
        """Parses the rest of the term after a factor."""
        if not self.curr:
            return left
        if self.curr[0] == TT_OP and self.curr[1] == "*":
            self.advance()
            right: Expr = self.parse_factor()
            return self.parse_term_tail(Mul(left, right))
        return left

    def parse_factor(self) -> Expr:
        """Parses a factor."""
        if not self.curr:
            raise ValueError(f"Unexpected eof at {self.tokens[-1][2]}")

        if self.curr[0] == TT_VAR:
            self.advance()
            if self.curr and self.curr[0] == TT_OP and self.curr[1] == "^":
                self.advance()
                exponent: str = self.parse_float()
                return Mono(float(exponent))
            return Mono(1.0)

        if self.curr[0] == TT_LPAREN:
            lpar_idx: int = self.curr[2]
            self.advance()
            expr: Expr = self.parse_expr()
            if not self.curr:
                raise ValueError(
                    f"Unexpected eof at {self.tokens[-1][2]} "
                    + f"(Expected ')' to match '(' at {lpar_idx})"
                )
            self.advance()
            return expr

        c: str = self.parse_float()
        if not self.curr:
            return Scl(float(c), Mono(0.0))
        if self.curr[0] == TT_OP and self.curr[1] == "^":
            if c != "2":
                raise ValueError(
                    f"General-base exponentiation not allowed (Got {c} at {self.curr[2]})"
                )
            self.advance()
            if self.curr[0] == TT_VAR:
                self.advance()
                return Exp()
            raise ValueError(
                f"General-power exponentiation not allowed (Got {self.curr[1]} at {self.curr[2]})"
            )
        if self.curr[0] == TT_OP and self.curr[1] == "*":
            self.advance()
            return Scl(float(c), self.parse_factor())
        return Scl(float(c), Mono(0.0))

    def parse_float(self) -> str:
        """Parses a float, including negative signs."""
        if not self.curr:
            raise ValueError(
                f"Unexpected eof at {self.tokens[-1][2]} (Expected number)"
            )
        neg: bool = False
        while self.curr and self.curr[0] == TT_OP and self.curr[1] == "-":
            neg = not neg
            self.advance()
        if self.curr[0] != TT_NUM:
            raise ValueError(
                f"Unexpected token at {self.curr[2]}: {self.curr[1]} (Expected number)"
            )
        c: str = self.curr[1]
        self.advance()
        if neg:
            c = "-" + c
        return c

    def parse(self) -> Expr:
        """Parses the entire expression."""
        expr: Expr = self.parse_expr()
        if self.curr:
            raise ValueError(
                f"Unexpected token at {self.curr[2]}: {self.curr[1]} (Expected eof)"
            )
        return expr


def parse(expr: str) -> Expr:
    """Parses the given expression string into an Expr tree."""
    return Parser(Lexer(expr).tokenize()).parse()
