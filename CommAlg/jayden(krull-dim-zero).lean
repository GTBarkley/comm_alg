import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.JacobsonIdeal
import Mathlib.RingTheory.Noetherian
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Artinian
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.RingTheory.Nilpotent
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Maximal
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Noetherian
import Mathlib.Data.Finite.Defs
import Mathlib.Order.Height
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.RingTheory.Finiteness
import Mathlib.Util.PiNotation

open PiNotation

namespace Ideal

variable (R : Type _) [CommRing R] (P : PrimeSpectrum R)

noncomputable def height : ℕ∞ := Set.chainHeight {J : PrimeSpectrum R | J < P}

noncomputable def krullDim (R : Type) [CommRing R] :
     WithBot ℕ∞ := ⨆ (I : PrimeSpectrum R), height R I

--variable {R}

-- Stacks Lemma 10.26.1 (Should already exists)
-- (1) The closure of a prime P is V(P)
-- (2) the irreducible closed subsets are V(P) for P prime
-- (3) the irreducible components are V(P) for P minimal prime

-- Stacks Definition 10.32.1: An ideal is locally nilpotent
-- if every element is nilpotent
class IsLocallyNilpotent {R : Type _} [CommRing R] (I : Ideal R) : Prop :=
    h : ∀ x ∈ I, IsNilpotent x
#check Ideal.IsLocallyNilpotent
end Ideal


-- Repeats the definition of the length of a module by Monalisa
variable (R : Type _) [CommRing R] (I J : Ideal R)
variable (M : Type _) [AddCommMonoid M] [Module R M]

-- change the definition of length of a module
namespace Module
noncomputable def length := Set.chainHeight {M' : Submodule R M | M' < ⊤}
end Module

-- Stacks Lemma 10.31.5: R is Noetherian iff Spec(R) is a Noetherian space
example [IsNoetherianRing R] :
    TopologicalSpace.NoetherianSpace (PrimeSpectrum R) :=
  inferInstance

instance ring_Noetherian_of_spec_Noetherian
    [TopologicalSpace.NoetherianSpace (PrimeSpectrum R)] :
    IsNoetherianRing R where
  noetherian := by sorry

lemma ring_Noetherian_iff_spec_Noetherian : IsNoetherianRing R 
    ↔ TopologicalSpace.NoetherianSpace (PrimeSpectrum R) := by
    constructor
    intro RisNoetherian
    -- how do I apply an instance to prove one direction?


-- Use TopologicalSpace.NoetherianSpace.exists_finset_irreducible :
-- Every closed subset of a noetherian space is a finite union 
-- of irreducible closed subsets.

-- Stacks Lemma 10.32.5: R Noetherian. I,J ideals.
--  If J ⊂ √I, then J ^ n ⊂ I for some n. In particular, locally nilpotent
-- and nilpotent are the same for Noetherian rings
lemma containment_radical_power_containment : 
    IsNoetherianRing R ∧ J ≤ Ideal.radical I → ∃ n : ℕ, J ^ n ≤ I :=  by 
    rintro ⟨RisNoetherian, containment⟩ 
    rw [isNoetherianRing_iff_ideal_fg] at RisNoetherian
    specialize RisNoetherian (Ideal.radical I)
    -- rcases RisNoetherian with ⟨S, Sgenerates⟩
    have containment2 : ∃ n : ℕ,  (Ideal.radical I) ^ n ≤ I := by
      apply Ideal.exists_radical_pow_le_of_fg I RisNoetherian
    cases' containment2 with n containment2'
    have containment3 : J ^ n ≤ (Ideal.radical I) ^ n := by 
      apply Ideal.pow_mono containment
    use n
    apply le_trans containment3 containment2'
-- The above can be proven using the following quicker theorem that is in the wrong place.
-- Ideal.exists_pow_le_of_le_radical_of_fG


-- Stacks Lemma 10.52.5: R → S is a ring map.  M is an S-mod. 
-- Then length_R M ≥ length_S M. 
-- Stacks Lemma 10.52.5': equality holds if R → S is surjective.

-- Stacks Lemma 10.52.6: I is a maximal ideal and IM = 0. Then length of M is
-- the same as the dimension as a vector space over R/I,
lemma length_eq_dim_if_maximal_annihilates {I : Ideal R} [Ideal.IsMaximal I] 
    : I • (⊤ : Submodule R M) = 0
     → Module.length R M = Module.rank R⧸I M⧸(I • (⊤ : Submodule R M)) := by sorry

-- Does lean know that M/IM is a R/I module?
-- Use 10.52.5

-- Stacks Lemma 10.52.8: I is a finitely generated maximal ideal of R.
-- M is a finite R-mod and I^nM=0. Then length of M is finite.
lemma power_zero_finite_length [Ideal.IsMaximal I] (h₁ : Ideal.FG I) [Module.Finite R M]
    (h₂ : (∃ n : ℕ, (I ^ n) • (⊤ : Submodule R M) = 0)) :
     (∃ m : ℕ, Module.length R M ≤ m) := by sorry
    -- intro IisFG IisMaximal MisFinite power
    -- rcases power with ⟨n, npower⟩
    -- how do I get a generating set?

open Finset

-- Stacks Lemma 10.53.3: R is Artinian iff R has finitely many maximal ideals
lemma Artinian_has_finite_max_ideal 
    [IsArtinianRing R] : Finite (MaximalSpectrum R) := by 
    by_contra infinite
    simp only [not_finite_iff_infinite] at infinite
    let m' : ℕ ↪ MaximalSpectrum R := Infinite.natEmbedding (MaximalSpectrum R)
    have m'inj := m'.injective
    let m'' : ℕ → Ideal R := fun n : ℕ ↦ ⨅ k ∈ range n, (m' k).asIdeal
    have comaximal : ∀ i j : ℕ, i ≠ j → (m' i).asIdeal ⊔ (m' j).asIdeal =
      (⊤ : Ideal R) := by 
      intro i j distinct
      apply Ideal.IsMaximal.coprime_of_ne
      sorry
      sorry
      --  by_contra equal
      have : (m' i) ≠ (m' j) := by 
        exact Function.Injective.ne m'inj distinct
      intro h
      apply this
      exact MaximalSpectrum.ext _ _ h
    -- let g :`= Ideal.quotientInfRingEquivPiQuotient m' comaximal


-- Stacks Lemma 10.53.4: R Artinian => Jacobson ideal of R is nilpotent
lemma Jacobson_of_Artinian_is_nilpotent 
    [IsArtinianRing R] : IsNilpotent (Ideal.jacobson (⊥ : Ideal R)) := by 
    have J := Ideal.jacobson (⊥ : Ideal R)
    

-- Stacks Lemma 10.53.5: If R has finitely many maximal ideals and 
-- locally nilpotent Jacobson radical, then R is the product of its localizations at 
-- its maximal ideals. Also, all primes are maximal
abbrev Prod_of_localization :=
  Π I : MaximalSpectrum R, Localization.AtPrime I.1

-- instance : CommRing (Prod_of_localization R) := by
--   unfold Prod_of_localization
--   infer_instance
     
def foo : Prod_of_localization R →+* R where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry
  map_add' := sorry


def product_of_localization_at_maximal_ideal [Finite (MaximalSpectrum R)]
    (h : Ideal.IsLocallyNilpotent (Ideal.jacobson (⊥ : Ideal R))) :
    Prod_of_localization R ≃+* R := by sorry

-- Stacks Lemma 10.53.6: R is Artinian iff R has finite length as an R-mod
lemma IsArtinian_iff_finite_length : 
    IsArtinianRing R ↔ (∃ n : ℕ, Module.length R R ≤ n) := by sorry 

-- Lemma: if R has finite length as R-mod, then R is Noetherian
lemma finite_length_is_Noetherian : 
    (∃ n : ℕ, Module.length R R ≤ n) → IsNoetherianRing R := by sorry 

-- Lemma: if R is Artinian then all the prime ideals are maximal
lemma primes_of_Artinian_are_maximal
    [IsArtinianRing R] [Ideal.IsPrime I] : Ideal.IsMaximal I := by sorry

-- Lemma: Krull dimension of a ring is the supremum of height of maximal ideals


-- Stacks Lemma 10.60.5: R is Artinian iff R is Noetherian of dimension 0
lemma dim_zero_Noetherian_iff_Artinian (R : Type _) [CommRing R] : 
    IsNoetherianRing R ∧ Ideal.krullDim R = 0 ↔ IsArtinianRing R := by 
    constructor
    sorry
    intro RisArtinian
    constructor
    apply finite_length_is_Noetherian
    rwa [IsArtinian_iff_finite_length] at RisArtinian
    sorry




    















