# Asymptotic Analysis as an Abstract Interpretation

This project is an implementation of asymptotic analysis of polynomials. Our preprint on this topic analyzes this analysis as an instance of abstract interpretation, and proves the soundness of the algorithm implemented in the [`asymptotic.py`](asymptotic.py) file.

## Features

- **Interactive Shell:** Evaluate, analyze, and fuzz expressions interactively with [`shell.py`](shell.py).
- **Fuzzer:** Randomly generate and tests expressions for analysis correctness in [`fuzzer.py`](fuzzer.py).
- **Unit Tests:** Basic correctness tests in [`test.py`](test.py).

## Requirements

- Python 3.10 or higher.

## Usage

```sh
git clone https://github.com/pingpingy1/asymp_as_absi.git
cd asymp_as_absi
python shell.py   # Run interactive shell
python fuzzer.py  # Perform fuzzer
python test.py    # Run unit tests
```