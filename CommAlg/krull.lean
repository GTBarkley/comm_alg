import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.FiniteType
import Mathlib.Order.Height
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.RingTheory.Ideal.MinimalPrime
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

/-- If something is smaller that Bot of a PartialOrder after attaching another Bot, it must be Bot. -/
lemma lt_bot_eq_WithBot_bot [PartialOrder α] [OrderBot α] {a : WithBot α} (h : a < (⊥ : α)) : a = ⊥ := by
  cases a
  . rfl
  . cases h.not_le (WithBot.coe_le_coe.2 bot_le)

namespace Ideal
open LocalRing

variable {R : Type _} [CommRing R] (I : PrimeSpectrum R)

/-- Definitions -/
noncomputable def height : ℕ∞ := Set.chainHeight {J : PrimeSpectrum R | J < I}
noncomputable def krullDim (R : Type _) [CommRing R] : WithBot ℕ∞ := ⨆ (I : PrimeSpectrum R), height I
noncomputable def codimension (J : Ideal R) : WithBot ℕ∞ := ⨅ I ∈ {I : PrimeSpectrum R | J ≤ I.asIdeal}, height I

lemma height_def : height I = Set.chainHeight {J : PrimeSpectrum R | J < I} := rfl
lemma krullDim_def (R : Type _) [CommRing R] : krullDim R = (⨆ (I : PrimeSpectrum R), height I : WithBot ℕ∞) := rfl
lemma krullDim_def' (R : Type _) [CommRing R] : krullDim R = iSup (λ I : PrimeSpectrum R => (height I : WithBot ℕ∞)) := rfl

/-- A lattice structure on WithBot ℕ∞. -/
noncomputable instance : CompleteLattice (WithBot (ℕ∞)) := WithBot.WithTop.completeLattice

/-- Height of ideals is monotonic. -/
lemma height_le_of_le {I J : PrimeSpectrum R} (I_le_J : I ≤ J) : height I ≤ height J := by
  apply Set.chainHeight_mono
  intro J' hJ'
  show J' < J
  exact lt_of_lt_of_le hJ' I_le_J

lemma krullDim_le_iff (R : Type _) [CommRing R] (n : ℕ) :
  krullDim R ≤ n ↔ ∀ I : PrimeSpectrum R, (height I : WithBot ℕ∞) ≤ ↑n := iSup_le_iff (α := WithBot ℕ∞)

lemma krullDim_le_iff' (R : Type _) [CommRing R] (n : ℕ∞) :
  krullDim R ≤ n ↔ ∀ I : PrimeSpectrum R, (height I : WithBot ℕ∞) ≤ ↑n := iSup_le_iff (α := WithBot ℕ∞)

@[simp]
lemma height_le_krullDim (I : PrimeSpectrum R) : height I ≤ krullDim R := 
  le_iSup (λ I : PrimeSpectrum R => (height I : WithBot ℕ∞)) I

/-- In a domain, the height of a prime ideal is Bot (0 in this case) iff it's the Bot ideal. -/
@[simp]
lemma height_bot_iff_bot {D: Type} [CommRing D] [IsDomain D] {P : PrimeSpectrum D} : height P = ⊥ ↔ P = ⊥ := by
  constructor
  · intro h
    unfold height at h
    rw [bot_eq_zero] at h
    simp only [Set.chainHeight_eq_zero_iff] at h
    apply eq_bot_of_minimal
    intro I
    by_contra x
    have : I ∈ {J | J < P} := x
    rw [h] at this
    contradiction
  · intro h
    unfold height
    simp only [bot_eq_zero', Set.chainHeight_eq_zero_iff]
    by_contra spec
    change _ ≠ _ at spec
    rw [← Set.nonempty_iff_ne_empty] at spec
    obtain ⟨J, JlP : J < P⟩ := spec
    have JneP : J ≠ P := ne_of_lt JlP
    rw [h, ←bot_lt_iff_ne_bot, ←h] at JneP
    have := not_lt_of_lt JneP
    contradiction

/-- The Krull dimension of a ring being ≥ n is equivalent to there being an
    ideal of height ≥ n. -/
lemma le_krullDim_iff (R : Type _) [CommRing R] (n : ℕ) :
  n ≤ krullDim R ↔ ∃ I : PrimeSpectrum R, n ≤ (height I : WithBot ℕ∞) := by
  constructor
  · unfold krullDim
    intro H
    by_contra H1
    push_neg at H1
    by_cases n ≤ 0
    · rw [Nat.le_zero] at h
      rw [h] at H H1
      have : ∀ (I : PrimeSpectrum R), ↑(height I) = (⊥ : WithBot ℕ∞) := by
        intro I
        specialize H1 I
        exact lt_bot_eq_WithBot_bot H1
      rw [←iSup_eq_bot] at this
      have := le_of_le_of_eq H this
      rw [le_bot_iff] at this
      exact WithBot.coe_ne_bot this
    · push_neg at h
      have : (n: ℕ∞) > 0 := Nat.cast_pos.mpr h
      replace H1 : ∀ (I : PrimeSpectrum R), height I ≤ n - 1 := by
        intro I
        specialize H1 I
        apply ENat.le_of_lt_add_one
        rw [←ENat.coe_one, ←ENat.coe_sub, ←ENat.coe_add, tsub_add_cancel_of_le]
        exact WithBot.coe_lt_coe.mp H1
        exact h
      replace H1 : ∀ (I : PrimeSpectrum R), (height I : WithBot ℕ∞) ≤ ↑(n - 1):=
          fun _ ↦ (WithBot.coe_le rfl).mpr (H1 _)
      rw [←iSup_le_iff] at H1
      have : ((n : ℕ∞) : WithBot ℕ∞) ≤ (((n  - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := le_trans H H1
      norm_cast at this
      have that : n - 1 < n := by refine Nat.sub_lt h (by norm_num)
      apply lt_irrefl (n-1) (trans that this)
  · rintro ⟨I, h⟩
    have : height I ≤ krullDim R := by apply height_le_krullDim
    exact le_trans h this

#check ENat.recTopCoe

/- terrible place for this lemma. Also this probably exists somewhere
  Also this is a terrible proof
-/
lemma eq_top_iff (n : WithBot ℕ∞) : n = ⊤ ↔ ∀ m : ℕ, m ≤ n := by
  aesop
  induction' n using WithBot.recBotCoe with n
  . exfalso
    have := (a 0)
    simp [not_lt_of_ge] at this
  induction' n using ENat.recTopCoe with n
  . rfl
  . have := a (n + 1)
    exfalso
    change (((n + 1) : ℕ∞) : WithBot ℕ∞) ≤ _ at this
    simp [WithBot.coe_le_coe] at this
    change ((n + 1) : ℕ∞) ≤ (n : ℕ∞) at this
    simp [ENat.add_one_le_iff] at this

lemma krullDim_eq_top_iff (R : Type _) [CommRing R] :
  krullDim R = ⊤ ↔ ∀ (n : ℕ), ∃ I : PrimeSpectrum R, n ≤ height I := by
  simp [eq_top_iff, le_krullDim_iff]
  change (∀ (m : ℕ), ∃ I, ((m : ℕ∞) : WithBot ℕ∞) ≤ height I) ↔ _
  simp [WithBot.coe_le_coe]
  

/-- The Krull dimension of a local ring is the height of its maximal ideal. -/
lemma krullDim_eq_height [LocalRing R] : krullDim R = height (closedPoint R) := by
  apply le_antisymm
  . rw [krullDim_le_iff']
    intro I
    apply WithBot.coe_mono
    apply height_le_of_le
    apply le_maximalIdeal
    exact I.2.1
  . simp only [height_le_krullDim]

/-- The height of a prime `𝔭` is greater than `n` if and only if there is a chain of primes less than `𝔭`
  with length `n + 1`. -/
lemma lt_height_iff' {𝔭 : PrimeSpectrum R} {n : ℕ∞} : 
n < height 𝔭 ↔ ∃ c : List (PrimeSpectrum R), c.Chain' (· < ·) ∧ (∀ 𝔮 ∈ c, 𝔮 < 𝔭) ∧ c.length = n + 1 := by
  match n with
  | ⊤ =>  
    constructor <;> intro h <;> exfalso
    . exact (not_le.mpr h) le_top
    . tauto
  | (n : ℕ) => 
    have (m : ℕ∞) : n < m ↔ (n + 1 : ℕ∞) ≤ m := by
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

/-- Form of `lt_height_iff''` for rewriting with the height coerced to `WithBot ℕ∞`. -/
lemma lt_height_iff'' {𝔭 : PrimeSpectrum R} {n : ℕ∞} : 
(n : WithBot ℕ∞) < height 𝔭 ↔ ∃ c : List (PrimeSpectrum R), c.Chain' (· < ·) ∧ (∀ 𝔮 ∈ c, 𝔮 < 𝔭) ∧ c.length = n + 1 := by
  rw [WithBot.coe_lt_coe]
  exact lt_height_iff'

#check height_le_krullDim
--some propositions that would be nice to be able to eventually

/-- The prime spectrum of the zero ring is empty. -/
lemma primeSpectrum_empty_of_subsingleton (x : PrimeSpectrum R) [Subsingleton R] : False :=
  x.1.ne_top_iff_one.1 x.2.1 <| Eq.substr (Subsingleton.elim 1 (0 : R)) x.1.zero_mem

/-- A CommRing has empty prime spectrum if and only if it is the zero ring. -/
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

/-- Nonzero rings have Krull dimension in ℕ∞ -/
lemma krullDim_nonneg_of_nontrivial (R : Type _) [CommRing R] [Nontrivial R] : ∃ n : ℕ∞, Ideal.krullDim R = n := by
  have h := dim_eq_bot_iff.not.mpr (not_subsingleton R)
  lift (Ideal.krullDim R) to ℕ∞ using h with k
  use k

/-- An ideal which is less than a prime is not a maximal ideal. -/
lemma not_maximal_of_lt_prime {p : Ideal R} {q : Ideal R} (hq : IsPrime q) (h : p < q) : ¬IsMaximal p := by
  intro hp
  apply IsPrime.ne_top hq
  apply (IsCoatom.lt_iff hp.out).mp
  exact h

/-- Krull dimension is ≤ 0 if and only if all primes are maximal. -/
lemma dim_le_zero_iff : krullDim R ≤ 0 ↔ ∀ I : PrimeSpectrum R, IsMaximal I.asIdeal := by
  show ((_ : WithBot ℕ∞) ≤ (0 : ℕ)) ↔ _
  rw [krullDim_le_iff R 0]
  constructor <;> intro h I
  . contrapose! h
    have ⟨𝔪, h𝔪⟩ := I.asIdeal.exists_le_maximal (IsPrime.ne_top I.IsPrime)
    let 𝔪p := (⟨𝔪, IsMaximal.isPrime h𝔪.1⟩ : PrimeSpectrum R)
    have hstrct : I < 𝔪p := by
      apply lt_of_le_of_ne h𝔪.2
      intro hcontr
      rw [hcontr] at h
      exact h h𝔪.1
    use 𝔪p
    show (0 : ℕ∞) < (_ : WithBot ℕ∞) 
    rw [lt_height_iff'']
    use [I]
    constructor
    . exact List.chain'_singleton _
    . constructor
      . intro I' hI'
        simp only [List.mem_singleton] at hI' 
        rwa [hI']
      . simp only [List.length_singleton, Nat.cast_one, zero_add]
  . contrapose! h
    change (0 : ℕ∞) < (_ : WithBot ℕ∞) at h
    rw [lt_height_iff''] at h
    obtain ⟨c, _, hc2, hc3⟩ := h
    norm_cast at hc3
    rw [List.length_eq_one] at hc3
    obtain ⟨𝔮, h𝔮⟩ := hc3
    use 𝔮
    specialize hc2 𝔮 (h𝔮 ▸ (List.mem_singleton.mpr rfl))
    apply not_maximal_of_lt_prime I.IsPrime
    exact hc2

/-- For a nonzero ring, Krull dimension is 0 if and only if all primes are maximal. -/
lemma dim_eq_zero_iff [Nontrivial R] : krullDim R = 0 ↔ ∀ I : PrimeSpectrum R, IsMaximal I.asIdeal := by
  rw [←dim_le_zero_iff]
  obtain ⟨n, hn⟩ := krullDim_nonneg_of_nontrivial R
  have : n ≥ 0 := zero_le n
  change _ ≤ _ at this
  rw [←WithBot.coe_le_coe,←hn] at this
  change (0 : WithBot ℕ∞) ≤ _ at this
  constructor <;> intro h'
  . rw [h']
  . exact le_antisymm h' this

/-- In a field, the unique prime ideal is the zero ideal. -/
@[simp]
lemma field_prime_bot {K: Type _} [Field K] {P : Ideal K} : IsPrime P ↔ P = ⊥ := by
      constructor
      · intro primeP
        obtain T := eq_bot_or_top P
        have : ¬P = ⊤ := IsPrime.ne_top primeP
        tauto
      · intro botP
        rw [botP]
        exact bot_prime

/-- In a field, all primes have height 0. -/
lemma field_prime_height_bot {K: Type _} [Nontrivial K] [Field K] {P : PrimeSpectrum K} : height P = ⊥ := by
    -- This should be doable by
    -- have : IsPrime P.asIdeal := P.IsPrime
    -- rw [field_prime_bot] at this
    -- have : P = ⊥ := PrimeSpectrum.ext P ⊥ this
    -- rw [height_bot_iff_bot]
    -- Need to check what's happening
    rw [bot_eq_zero]
    unfold height
    simp only [Set.chainHeight_eq_zero_iff]
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

/-- The Krull dimension of a field is 0. -/
lemma dim_field_eq_zero {K : Type _} [Field K] : krullDim K = 0 := by
  unfold krullDim
  simp only [field_prime_height_bot, ciSup_unique]

/-- A domain with Krull dimension 0 is a field. -/
lemma domain_dim_zero.isField {D: Type _} [CommRing D] [IsDomain D] (h: krullDim D = 0) : IsField D := by
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
    exact not_le_of_gt (ENat.one_le_iff_pos.mp this)
  have nonpos_height : height P' ≤ 0 := by
    have := height_le_krullDim P'
    rw [h] at this
    aesop
  contradiction

/-- A domain has Krull dimension 0 if and only if it is a field. -/
lemma domain_dim_eq_zero_iff_field {D: Type _} [CommRing D] [IsDomain D] : krullDim D = 0 ↔ IsField D := by
  constructor
  · exact domain_dim_zero.isField
  · intro fieldD
    let h : Field D := fieldD.toField
    exact dim_field_eq_zero

#check Ring.DimensionLEOne
-- This lemma is false!
lemma dim_le_one_iff : krullDim R ≤ 1 ↔ Ring.DimensionLEOne R := sorry

/-- The converse of this is false, because the definition of "dimension ≤ 1" in mathlib
  applies only to dimension zero rings and domains of dimension 1. -/
lemma dim_le_one_of_dimLEOne :  Ring.DimensionLEOne R → krullDim R ≤ 1 := by
  show _ → ((_ : WithBot ℕ∞) ≤ (1 : ℕ))
  rw [krullDim_le_iff R 1]
  intro H p
  apply le_of_not_gt
  intro h
  rcases (lt_height_iff''.mp h) with ⟨c, ⟨hc1, hc2, hc3⟩⟩
  norm_cast at hc3
  rw [List.chain'_iff_get] at hc1
  specialize hc1 0 (by rw [hc3]; simp only)
  set q0 : PrimeSpectrum R := List.get c { val := 0, isLt := _ }
  set q1 : PrimeSpectrum R := List.get c { val := 1, isLt := _ } 
  specialize hc2 q1 (List.get_mem _ _ _)
  change q0.asIdeal < q1.asIdeal at hc1
  have q1nbot := Trans.trans (bot_le : ⊥ ≤ q0.asIdeal) hc1
  specialize H q1.asIdeal (bot_lt_iff_ne_bot.mp q1nbot) q1.IsPrime
  exact (not_maximal_of_lt_prime p.IsPrime hc2) H

/-- The Krull dimension of a PID is at most 1. -/
lemma dim_le_one_of_pid [IsDomain R] [IsPrincipalIdealRing R] : krullDim R ≤ 1 := by
  rw [dim_le_one_iff]
  exact Ring.DimensionLEOne.principal_ideal_ring R

lemma dim_le_dim_polynomial_add_one [Nontrivial R] :
  krullDim R + 1 ≤ krullDim (Polynomial R) := sorry

-- lemma dim_eq_dim_polynomial_add_one [Nontrivial R] [IsNoetherianRing R] :
--   krullDim R + 1 = krullDim (Polynomial R) := sorry

lemma krull_height_theorem [Nontrivial R] [IsNoetherianRing R] (P: PrimeSpectrum R) (S: Finset R)
  (h: P.asIdeal ∈ Ideal.minimalPrimes (Ideal.span S)) : height P ≤ S.card := by
  sorry

lemma dim_mvPolynomial [Field K] (n : ℕ) : krullDim (MvPolynomial (Fin n) K) = n := sorry

lemma height_eq_dim_localization :
  height I = krullDim (Localization.AtPrime I.asIdeal) := sorry

lemma dim_quotient_le_dim : height I + krullDim (R ⧸ I.asIdeal) ≤ krullDim R := sorry

lemma height_add_dim_quotient_le_dim : height I + krullDim (R ⧸ I.asIdeal) ≤ krullDim R := sorry