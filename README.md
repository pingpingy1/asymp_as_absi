# Asymptotic Analysis as Abstract Interpretation

This project accompanies the paper **“Asymptotic Analysis as Abstract Interpretation.”**  
It implements an asymptotic analysis of polynomial functions and formalizes the underlying theory as an instance of abstract interpretation.

The repository contains:
- an executable **interactive shell** for exploring asymptotic behavior,
- a **fuzzer** for automatic validation of analysis correctness,
- and a **Lean 4 mechanization** that defines the formal semantics and verifies key properties of the framework.

## Features

- **Interactive Shell** — Evaluate, analyze, and fuzz expressions interactively in [`shell.py`](shell/shell.py).  
- **Fuzzer** — Automatically generate and test random expressions for semantic correctness in [`fuzzer.py`](shell/fuzzer.py).  
- **Unit Tests** — Basic regression tests in [`test.py`](shell/test.py).  
- **Lean Formalization** — Formal definitions and partial proofs of the framework in [`LeanProof`](LeanProof/).  

## Requirements

- **Python** ≥ 3.10  
- **Lean** ≥ 4.25.0-rc2  
- **Mathlib4**

## Usage

```bash
git clone https://github.com/pingpingy1/asymp_as_absi.git
cd asymp_as_absi/shell

# Run the interactive shell
python shell.py

# Run the fuzzer
python fuzzer.py

# Run unit tests
python test.py
```
