import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.FiniteType
import Mathlib.Order.Height
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/- This file contains the definitions of height of an ideal, and the krull
  dimension of a commutative ring.
  There are also sorried statements of many of the theorems that would be
  really nice to prove.
  I'm imagining for this file to ultimately contain basic API for height and
  krull dimension, and the theorems will probably end up other files,
  depending on how long the proofs are, and what extra API needs to be
  developed.
-/

namespace Ideal
open LocalRing

variable {R : Type _} [CommRing R] (I : PrimeSpectrum R)

noncomputable def height : ℕ∞ := Set.chainHeight {J : PrimeSpectrum R | J < I}

noncomputable def krullDim (R : Type _) [CommRing R] : WithBot ℕ∞ := ⨆ (I : PrimeSpectrum R), height I

lemma height_def : height I = Set.chainHeight {J : PrimeSpectrum R | J < I} := rfl
lemma krullDim_def (R : Type _) [CommRing R] : krullDim R = (⨆ (I : PrimeSpectrum R), height I : WithBot ℕ∞) := rfl
lemma krullDim_def' (R : Type _) [CommRing R] : krullDim R = iSup (λ I : PrimeSpectrum R => (height I : WithBot ℕ∞)) := rfl

noncomputable instance : CompleteLattice (WithBot (ℕ∞)) := WithBot.WithTop.completeLattice

lemma height_le_of_le {I J : PrimeSpectrum R} (I_le_J : I ≤ J) : height I ≤ height J := by
  apply Set.chainHeight_mono
  intro J' hJ'
  show J' < J
  exact lt_of_lt_of_le hJ' I_le_J

lemma krullDim_le_iff (R : Type _) [CommRing R] (n : ℕ) :
  krullDim R ≤ n ↔ ∀ I : PrimeSpectrum R, (height I : WithBot ℕ∞) ≤ ↑n := iSup_le_iff (α := WithBot ℕ∞)

lemma krullDim_le_iff' (R : Type _) [CommRing R] (n : ℕ∞) :
  krullDim R ≤ n ↔ ∀ I : PrimeSpectrum R, (height I : WithBot ℕ∞) ≤ ↑n := iSup_le_iff (α := WithBot ℕ∞)

lemma le_krullDim_iff (R : Type _) [CommRing R] (n : ℕ) :
  n ≤ krullDim R ↔ ∃ I : PrimeSpectrum R, n ≤ (height I : WithBot ℕ∞) := by sorry

lemma le_krullDim_iff' (R : Type _) [CommRing R] (n : ℕ∞) :
  n ≤ krullDim R ↔ ∃ I : PrimeSpectrum R, n ≤ (height I : WithBot ℕ∞) := by sorry

@[simp]
lemma height_le_krullDim (I : PrimeSpectrum R) : height I ≤ krullDim R := 
  le_iSup (λ I : PrimeSpectrum R => (height I : WithBot ℕ∞)) I

lemma krullDim_eq_height [LocalRing R] : krullDim R = height (closedPoint R) := by
  apply le_antisymm
  . rw [krullDim_le_iff']
    intro I
    apply WithBot.coe_mono
    apply height_le_of_le
    apply le_maximalIdeal
    exact I.2.1
  . simp

#check height_le_krullDim
--some propositions that would be nice to be able to eventually

lemma primeSpectrum_empty_of_subsingleton (x : PrimeSpectrum R) [Subsingleton R] : False :=
  x.1.ne_top_iff_one.1 x.2.1 <| Eq.substr (Subsingleton.elim 1 (0 : R)) x.1.zero_mem

lemma primeSpectrum_empty_iff : IsEmpty (PrimeSpectrum R) ↔ Subsingleton R := by
  constructor
  . contrapose
    rw [not_isEmpty_iff, ←not_nontrivial_iff_subsingleton, not_not]
    apply PrimeSpectrum.instNonemptyPrimeSpectrum
  . intro h
    by_contra hneg
    rw [not_isEmpty_iff] at hneg
    rcases hneg with ⟨a, ha⟩
    exact primeSpectrum_empty_of_subsingleton ⟨a, ha⟩

/-- A ring has Krull dimension -∞ if and only if it is the zero ring -/
lemma dim_eq_bot_iff : krullDim R = ⊥ ↔ Subsingleton R := by
  unfold Ideal.krullDim
  rw [←primeSpectrum_empty_iff, iSup_eq_bot]
  constructor <;> intro h
  . rw [←not_nonempty_iff]
    rintro ⟨a, ha⟩
    specialize h ⟨a, ha⟩
    tauto
  . rw [h.forall_iff]
    trivial

lemma dim_eq_zero_iff_field [IsDomain R] : krullDim R = 0 ↔ IsField R := by sorry

#check Ring.DimensionLEOne
lemma dim_le_one_iff : krullDim R ≤ 1 ↔ Ring.DimensionLEOne R := sorry

lemma dim_le_one_of_pid [IsDomain R] [IsPrincipalIdealRing R] : krullDim R ≤ 1 := by
  rw [dim_le_one_iff]
  exact Ring.DimensionLEOne.principal_ideal_ring R

lemma dim_le_dim_polynomial_add_one [Nontrivial R] :
  krullDim R ≤ krullDim (Polynomial R) + 1 := sorry

lemma dim_eq_dim_polynomial_add_one [Nontrivial R] [IsNoetherianRing R] :
  krullDim R = krullDim (Polynomial R) + 1 := sorry

lemma height_eq_dim_localization :
  height I = krullDim (Localization.AtPrime I.asIdeal) := sorry

lemma height_add_dim_quotient_le_dim : height I + krullDim (R ⧸ I.asIdeal) ≤ krullDim R := sorry