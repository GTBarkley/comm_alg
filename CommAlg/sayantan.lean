import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Order.Height
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
-- import Mathlib.Data.ENat.Lattice
-- import Mathlib.Order.OrderIsoNat
-- import Mathlib.Tactic.TFAE

namespace Ideal

-- def foo : List Nat := [1, 2, 3, 4, 5]

-- #check List.Chain'

-- example : List.Chain' (· < ·) foo := by
--   repeat { constructor; norm_num }
  
  

example (x : Nat) : List.Chain' (· < ·)  [x] := by
  constructor


  
variable {R : Type _} [CommRing R] (I : PrimeSpectrum R)

noncomputable def height : ℕ∞ := Set.chainHeight {J : PrimeSpectrum R | J < I}

noncomputable def krullDim (R : Type) [CommRing R] : WithBot ℕ∞ := ⨆ (I : PrimeSpectrum R), height I

lemma height_def : height I = Set.chainHeight {J : PrimeSpectrum R | J < I} := rfl
lemma krullDim_def (R : Type) [CommRing R] : krullDim R = (⨆ (I : PrimeSpectrum R), height I : WithBot ℕ∞) := rfl
lemma krullDim_def' (R : Type) [CommRing R] : krullDim R = iSup (λ I : PrimeSpectrum R => (height I : WithBot ℕ∞)) := rfl

variable {K : Type _} [Field K]

lemma dim_field_eq_zero : krullDim K = 0 := by
  have prime_bot (P : Ideal K) : IsPrime P ↔ P = ⊥ := by
      constructor
      · intro primeP
        obtain T := eq_bot_or_top P
        have : ¬P = ⊤ := IsPrime.ne_top primeP
        tauto
      · intro botP
        rw [botP]
        exact bot_prime
  unfold krullDim
  have height_zero : ∀ P : PrimeSpectrum K, height P = 0 := by
    intro P
    unfold height
    simp
    by_contra spec
    change _ ≠ _ at spec
    rw [← Set.nonempty_iff_ne_empty] at spec
    obtain ⟨J, JlP : J < P⟩ := spec
    have P0 : IsPrime P.asIdeal := P.IsPrime
    have J0 : IsPrime J.asIdeal := J.IsPrime
    rw [prime_bot] at P0 J0
    have : J.asIdeal = P.asIdeal := Eq.trans J0 (Eq.symm P0)
    have JeqP : J = P := PrimeSpectrum.ext J P this
    have JneqP : J ≠ P := ne_of_lt JlP
    contradiction
  simp [height_zero]