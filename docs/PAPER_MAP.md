# Correspondence with the mathematical proof

All declarations below are in `BentDecompositions.Family`, except the two-element sign helpers in `BentDecompositions`.

## Definitions

`Point n = Finset (Fin n)` represents the full binary cube by one-coordinate subsets. `BF n = Point n → ZMod 2` includes every Boolean function on it. `monomial T x` is one precisely when T is a subset of x. `evalANF` evaluates the squarefree polynomial with the given coefficients. `familyCoefficients n` selects all even degrees up to n/2, including degree zero; `Fn` is their sum.

`character u x = (-1)^|u∩x|` is the binary dot-product character. `Bent` requires every integer Walsh coefficient to be ±2^(n/2). The final theorem uses only even dimensions n=2^k≥8.

## Modules and argument

| Module | Role |
| --- | --- |
| `Signs` | Generic sign identities in the two-element field. |
| `Basic` | Cube, Walsh transform, bentness, ANF, degree and family definitions. |
| `Geometry` | Monomial counts and Hamming-ball complement bijections. |
| `WalshSupport`, `Support` | Lucas/Pascal calculation of the actual support of Fn. |
| `Walsh` | Walsh divisibility, parity conversion and affine output shifts. |
| `ArithmeticFour` | Modulo-four binomial identities and selected support counts. |
| `Restriction` | Orthogonality forces an affine restriction. |
| `Arithmetic` | Dyadic binomial valuations and discrepancy four modulo eight. |
| `Degree` | ANF uniqueness and exact degree, for all k≥3. |
| `Nonbent` | Weight/Walsh calculation proving Fn itself is not bent. |
| `Main` | Unconditional exclusion of two summands and then of at most two. |

The proof follows the four mathematical steps: support; orthogonality; affine restriction; normalization and the weight contradiction. The paper's dimension calculation in the affine-restriction step is implemented by an equivalent general triangular induction on subsets. No finite interpolation certificate replaces the all-dimensional argument.

`Fn_not_sum_two_bent` quantifies over all Boolean function pairs, with no construction-class or symmetry restriction. The normalized weight discrepancy must be divisible by 2^(n/2), but is four modulo eight. `Fn_not_bent` and `Fn_ne_zero` handle the remaining one- and zero-summand cases. `full_infinite_family` combines those results with exact degree.

This repository does not assert a three-bent decomposition, a lower bound above three summands, or a result in every non-dyadic even dimension. No novelty or journal-acceptance claim is implied by formal verification.

## Even dimension

`EvenDimension.lean` proves character orthogonality, integer Walsh–Parseval, and `Bent.even_dimension : Bent f → Even n`. Parseval and flat magnitude imply n=2*(n/2), so odd dimensions cannot satisfy the definition. The theorem includes n=0; no positivity or evenness hypothesis is assumed.
