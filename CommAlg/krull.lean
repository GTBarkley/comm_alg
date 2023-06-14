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

lemma krullDim_nonneg_of_nontrivial (R : Type _) [CommRing R] [Nontrivial R] : ∃ n : ℕ∞, Ideal.krullDim R = n := by
  have h := dim_eq_bot_iff.not.mpr (not_subsingleton R)
  lift (Ideal.krullDim R) to ℕ∞ using h with k
  use k

lemma dim_eq_zero_iff [Nontrivial R] : krullDim R = 0 ↔ ∀ I : PrimeSpectrum R, IsMaximal I.asIdeal := by
  constructor <;> intro h
  . intro I
    sorry
  . sorry
  
@[simp]
lemma field_prime_bot {K: Type _} [Field K] (P : Ideal K) : IsPrime P ↔ P = ⊥ := by
      constructor
      · intro primeP
        obtain T := eq_bot_or_top P
        have : ¬P = ⊤ := IsPrime.ne_top primeP
        tauto
      · intro botP
        rw [botP]
        exact bot_prime

lemma field_prime_height_zero {K: Type _} [Field K] (P : PrimeSpectrum K) : height P = 0 := by
    unfold height
    simp
    by_contra spec
    change _ ≠ _ at spec
    rw [← Set.nonempty_iff_ne_empty] at spec
    obtain ⟨J, JlP : J < P⟩ := spec
    have P0 : IsPrime P.asIdeal := P.IsPrime
    have J0 : IsPrime J.asIdeal := J.IsPrime
    rw [field_prime_bot] at P0 J0
    have : J.asIdeal = P.asIdeal := Eq.trans J0 (Eq.symm P0)
    have : J = P := PrimeSpectrum.ext J P this
    have : J ≠ P := ne_of_lt JlP
    contradiction

lemma dim_field_eq_zero {K : Type _} [Field K] : krullDim K = 0 := by
  unfold krullDim
  simp [field_prime_height_zero]

lemma isField.dim_zero {D: Type _} [CommRing D] [IsDomain D] (h: krullDim D = 0) : IsField D := by
  by_contra x
  rw [Ring.not_isField_iff_exists_prime] at x
  obtain ⟨P, ⟨h1, primeP⟩⟩ := x
  let P' : PrimeSpectrum D := PrimeSpectrum.mk P primeP
  have h2 : P' ≠ ⊥ := by
    by_contra a
    have : P = ⊥ := by rwa [PrimeSpectrum.ext_iff] at a
    contradiction
  have pos_height : ¬ (height P') ≤ 0  := by
    have : ⊥ ∈ {J | J < P'} := Ne.bot_lt h2
    have : {J | J < P'}.Nonempty := Set.nonempty_of_mem this
    unfold height
    rw [←Set.one_le_chainHeight_iff] at this
    exact not_le_of_gt (Iff.mp ENat.one_le_iff_pos this)
  have nonpos_height : height P' ≤ 0 := by
    have := height_le_krullDim P'
    rw [h] at this
    aesop
  contradiction

lemma dim_eq_zero_iff_field {D: Type _} [CommRing D] [IsDomain D] : krullDim D = 0 ↔ IsField D := by
  constructor
  · exact isField.dim_zero
  · intro fieldD
    let h : Field D := IsField.toField fieldD
    exact dim_field_eq_zero

#check Ring.DimensionLEOne
-- This lemma is false!
lemma dim_le_one_iff : krullDim R ≤ 1 ↔ Ring.DimensionLEOne R := sorry

lemma lt_height_iff' {𝔭 : PrimeSpectrum R} {n : ℕ∞} : 
height 𝔭 > n ↔ ∃ c : List (PrimeSpectrum R), c.Chain' (· < ·) ∧ (∀ 𝔮 ∈ c, 𝔮 < 𝔭) ∧ c.length = n + 1 := by
  rcases n with _ | n
  . constructor <;> intro h <;> exfalso
    . exact (not_le.mpr h) le_top
    . tauto
  have (m : ℕ∞) : m > some n ↔ m ≥ some (n + 1) := by
    symm
    show (n + 1 ≤ m ↔ _ )
    apply ENat.add_one_le_iff
    exact ENat.coe_ne_top _
  rw [this]
  unfold Ideal.height
  show ((↑(n + 1):ℕ∞) ≤ _) ↔ ∃c, _ ∧ _ ∧ ((_ : WithTop ℕ) = (_:ℕ∞))
  rw [{J | J < 𝔭}.le_chainHeight_iff]
  show (∃ c, (List.Chain' _ c ∧ ∀𝔮, 𝔮 ∈ c → 𝔮 < 𝔭) ∧ _) ↔ _
  constructor <;> rintro ⟨c, hc⟩ <;> use c
  . tauto
  . change _ ∧ _ ∧ (List.length c : ℕ∞) = n + 1 at hc
    norm_cast at hc
    tauto

lemma lt_height_iff'' {𝔭 : PrimeSpectrum R} {n : ℕ∞} : 
height 𝔭 > (n : WithBot ℕ∞) ↔ ∃ c : List (PrimeSpectrum R), c.Chain' (· < ·) ∧ (∀ 𝔮 ∈ c, 𝔮 < 𝔭) ∧ c.length = n + 1 := by
  show (_ < _) ↔ _
  rw [WithBot.coe_lt_coe]
  exact lt_height_iff'

/-- The converse of this is false, because the definition of "dimension ≤ 1" in mathlib
  applies only to dimension zero rings and domains of dimension 1. -/
lemma dim_le_one_of_dimLEOne :  Ring.DimensionLEOne R → krullDim R ≤ (1 : ℕ) := by
  rw [krullDim_le_iff R 1]
  intro H p
  apply le_of_not_gt
  intro h
  rcases (lt_height_iff''.mp h) with ⟨c, ⟨hc1, hc2, hc3⟩⟩
  norm_cast at hc3
  rw [List.chain'_iff_get] at hc1
  specialize hc1 0 (by rw [hc3]; simp)
  set q0 : PrimeSpectrum R := List.get c { val := 0, isLt := _ }
  set q1 : PrimeSpectrum R := List.get c { val := 1, isLt := _ } 
  specialize hc2 q1 (List.get_mem _ _ _)
  change q0.asIdeal < q1.asIdeal at hc1
  have q1nbot := Trans.trans (bot_le : ⊥ ≤ q0.asIdeal) hc1
  specialize H q1.asIdeal (bot_lt_iff_ne_bot.mp q1nbot) q1.IsPrime
  apply IsPrime.ne_top p.IsPrime
  apply (IsCoatom.lt_iff H.out).mp
  exact hc2

lemma dim_le_one_of_pid [IsDomain R] [IsPrincipalIdealRing R] : krullDim R ≤ 1 := by
  rw [dim_le_one_iff]
  exact Ring.DimensionLEOne.principal_ideal_ring R

lemma dim_le_dim_polynomial_add_one [Nontrivial R] :
  krullDim R + 1 ≤ krullDim (Polynomial R) := sorry

lemma dim_eq_dim_polynomial_add_one [Nontrivial R] [IsNoetherianRing R] :
  krullDim R + 1 = krullDim (Polynomial R) := sorry

lemma dim_mvPolynomial [Field K] (n : ℕ) : krullDim (MvPolynomial (Fin n) K) = n := sorry

lemma height_eq_dim_localization :
  height I = krullDim (Localization.AtPrime I.asIdeal) := sorry

lemma dim_quotient_le_dim : height I + krullDim (R ⧸ I.asIdeal) ≤ krullDim R := sorry

lemma height_add_dim_quotient_le_dim : height I + krullDim (R ⧸ I.asIdeal) ≤ krullDim R := sorry