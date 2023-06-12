import Mathlib.Order.KrullDimension
import Mathlib.Order.JordanHolder
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Order.Height
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.HomogeneousIdeal
import Mathlib.Algebra.Module.GradedModule
import Mathlib.RingTheory.Ideal.AssociatedPrime
import Mathlib.RingTheory.Noetherian

variable {ι σ R A : Type _}

section HomogeneousDef

variable [Semiring A]

variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ℤ → σ)

variable [GradedRing 𝒜]

variable (I : HomogeneousIdeal 𝒜)

-- def Ideal.IsHomogeneous : Prop :=
-- ∀ (i : ι) ⦃r : A⦄, r ∈ I → (DirectSum.decompose 𝒜 r i : A) ∈ I
-- #align ideal.is_homogeneous Ideal.IsHomogeneous

-- structure HomogeneousIdeal extends Submodule A A where
-- is_homogeneous' : Ideal.IsHomogeneous 𝒜 toSubmodule

--#check Ideal.IsPrime hI

def HomogeneousPrime (I : Ideal A):= Ideal.IsPrime I

def HomogeneousMax (I : Ideal A):= Ideal.IsMaximal I

--theorem monotone_stabilizes_iff_noetherian :
-- (∀ f : ℕ →o Submodule R M, ∃ n, ∀ m, n ≤ m → f n = f m) ↔ IsNoetherian R M := by
-- rw [isNoetherian_iff_wellFounded, WellFounded.monotone_chain_condition]