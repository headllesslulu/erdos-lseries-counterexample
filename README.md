# erdos-lseries-counterexample
An explicit period-11,025 counterexample to Erdős’s 1965 nonvanishing conjecture for periodic Dirichlet series, with an exact integer certificate and Lean 4 formalization.

# Erdős L-Series Counterexample

An explicit counterexample to Erdős’s nonvanishing conjecture
for periodic Dirichlet series, recorded by Livingston in 1965.

## Main Result

There exists a periodic function f of least period q = 11,025
such that:

- f(n) = 0 if and only if q divides n.
- f(n) ∈ {-1, 1} otherwise.
- Exactly 5,512 residues have each sign.
- The ordinary Dirichlet series ∑ f(n)/n converges to zero.

This provides a counterexample to the stated conjecture.

## Proof Method

The construction combines:

- Quadratic characters modulo 3, 5, and 7.
- Divisor-indexed character expansions.
- Exact integer cancellation identities.
- Harmonic asymptotics and Dirichlet's test.

The certificate contains seven weighted balance identities
and three prime-valuation cancellation identities.

The proof requires no assumptions about the zeros of
individual Dirichlet L-functions or the Riemann hypothesis.

## Repository Contents

- Erdos_LSeries_Counterexample.pdf — Mathematical proof.
- ErdosLSeries.lean — Lean 4 formalization.

## Verification

The finite certificate checks all 11,025 residues using exact
integer arithmetic.

The formalization establishes periodicity, coefficient
conditions, convergence to zero, and the negation of the
nonvanishing conjecture.

## Research Status

Explicit counterexample with a constructive proof and
formal verification framework.

## License

Apache License 2.0.
