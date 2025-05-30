from expr import Expr
from parse import parse

ING: bool = True


def execute_cmd(cmd: str) -> None:
    expr_str: str
    expr: Expr

    if cmd == "exit":
        global ING
        ING = False
    elif cmd.startswith("help"):
        print("Help!")
    elif cmd.startswith("eval"):
        idx: int = cmd.rfind("at")
        if idx < 0:
            print("Error: 'eval' command without 'at'")
        else:
            expr_str = cmd[4:idx].strip()
            at: str = cmd[idx + 2:].strip()
            try:
                expr = parse(expr_str)
                print(f"({expr})({at}) = {expr.eval(int(at))}")
            except ValueError as e:
                print(f"{e}")
    elif cmd.startswith("analyze"):
        expr_str = cmd[7:].strip()
        expr = parse(expr_str)
        print(expr)
        print("TODO")
    else:
        print(f"Unknown command: {cmd}")

if __name__ == "__main__":
    while ING:
        cmd: str = input(">>> ")
        execute_cmd(cmd.strip())
