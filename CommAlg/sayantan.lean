import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Order.Height
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace Ideal

example (x : Nat) : List.Chain' (· < ·)  [x] := by
  constructor


  
variable {R : Type _} [CommRing R] (I : PrimeSpectrum R)
noncomputable def height : ℕ∞ := Set.chainHeight {J : PrimeSpectrum R | J < I}
noncomputable def krullDim (R : Type) [CommRing R] : WithBot ℕ∞ := ⨆ (I : PrimeSpectrum R), height I

lemma height_def : height I = Set.chainHeight {J : PrimeSpectrum R | J < I} := rfl
lemma krullDim_def (R : Type) [CommRing R] : krullDim R = (⨆ (I : PrimeSpectrum R), height I : WithBot ℕ∞) := rfl
lemma krullDim_def' (R : Type) [CommRing R] : krullDim R = iSup (λ I : PrimeSpectrum R => (height I : WithBot ℕ∞)) := rfl

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
  unfold krullDim at h
  simp [height] at h
  by_contra x
  rw [Ring.not_isField_iff_exists_prime] at x
  obtain ⟨P, ⟨h, primeP⟩⟩ := x
  have PgtBot : P > ⊥ := Ne.bot_lt h
  sorry

lemma dim_eq_zero_iff_field {D: Type _} [CommRing D] [IsDomain D] : krullDim D = 0 ↔ IsField D := by
  constructor
  · exact isField.dim_zero
  · intro fieldD
    have : Field D := IsField.toField fieldD
    -- Not exactly sure why this is failing
    -- apply @dim_field_eq_zero D _
    sorry
