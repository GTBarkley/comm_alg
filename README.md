# Commutative algebra in Lean

Welcome to the repository for adding definitions and theorems related to Krull dimension and Hilbert polynomials to mathlib.

We start the commutative algebra project with a list of important definitions and theorems and go from there.

Feel free to add, modify, and expand this file. Below are starting points for the project:

- Definitions of an ideal, prime ideal, and maximal ideal:
```lean
def Mathlib.RingTheory.Ideal.Basic.Ideal (R : Type u) [Semiring R] := Submodule R R
```

- Definition of a Spec of a ring

- Definition of a Noetherian and Artinian rings

- Definitions of a local ring and quotient ring

- Definition of the chain of prime ideals and the length of these chains

- Definition of the Krull dimension (supremum of the lengh of chain of prime ideal) 

- Definition of the height of prime ideal (dimension of A_p)

Give Examples of each of the above cases for a particular instances of ring

Theorem 0: Hilbert Basis Theorem

Theorem 1: If A is a nonzero ring, then dim A[t] >= dim A +1

Theorem 2: If A is a nonzero noetherian ring, then dim A[t] = dim A + 1

Theorem 3: If A is nonzero ring then dim A_p + dim A/p <= dim A

Definition of a graded module
