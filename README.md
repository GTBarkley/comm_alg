# Commutative algebra in Lean

Welcome to the repository for adding definitions and theorems related to Krull dimension and Hilbert polynomials to mathlib.

We start the commutative algebra project with a list of important definitions and theorems and go from there.

Feel free to add, modify, and expand this file. Below are starting points for the project:

- Definitions of an ideal, prime ideal, and maximal ideal:
```lean
def Mathlib.RingTheory.Ideal.Basic.Ideal (R : Type u) [Semiring R] := Submodule R R
class Mathlib.RingTheory.Ideal.Basic.IsPrime (I : Ideal α) : Prop
class IsMaximal (I : Ideal α) : Prop
```

- Definition of a Spec of a ring: `Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic.PrimeSpectrum`

- Definition of a Noetherian and Artinian rings:
```lean
class Mathlib.RingTheory.Noetherian.IsNoetherian (R M) [Semiring R] [AddCommMonoid M] [Module R M] : Prop
class Mathlib.RingTheory.Artinian.IsArtinian (R M) [Semiring R] [AddCommMonoid M] [Module R M] : Prop
```
- Definition of a polynomial ring: `Mathlib.RingTheory.Polynomial.Basic`

- Definitions of a local ring and quotient ring: `Mathlib.RingTheory.Ideal.Quotient.?`
```lean
class Mathlib.RingTheory.Ideal.LocalRing.LocalRing (R : Type u) [Semiring R] extends Nontrivial R : Prop
```

- Definition of the chain of prime ideals and the length of these chains

- Definition of the Krull dimension (supremum of the lengh of chain of prime ideal): `Mathlib.Order.KrullDimension.krullDim`

- Krull dimension of a module

- Definition of the height of prime ideal (dimension of A_p): `Mathlib.Order.KrullDimension.height`


Give Examples of each of the above cases for a particular instances of ring

Theorem 0: Hilbert Basis Theorem:
```lean
theorem Mathlib.RingTheory.Polynomial.Basic.Polynomial.isNoetherianRing [inst : IsNoetherianRing R] : IsNoetherianRing R[X]
```

Theorem 1: If A is a nonzero ring, then dim A[t] >= dim A +1

Theorem 2: If A is a nonzero noetherian ring, then dim A[t] = dim A + 1

Theorem 3: If A is nonzero ring then dim A_p + dim A/p <= dim A

Lemma 0: A ring is artinian iff it is noetherian of dimension 0.

Definition of a graded module
