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
import Mathlib.RingTheory.Ideal.MinimalPrime
import CommAlg.krull

open PiNotation

namespace Ideal

variable (R : Type _) [CommRing R] (P : PrimeSpectrum R)

-- Stacks Definition 10.32.1: An ideal is locally nilpotent
-- if every element is nilpotent
class IsLocallyNilpotent {R : Type _} [CommRing R] (I : Ideal R) : Prop :=
    h : ∀ x ∈ I, IsNilpotent x
end Ideal

def RingJacobson (R) [Ring R] := Ideal.jacobson (⊥ : Ideal R)

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
    sorry
    sorry
    -- how do I apply an instance to prove one direction?

-- Stacks Lemma 5.9.2: 
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
-- lemma length_eq_dim_if_maximal_annihilates {I : Ideal R} [Ideal.IsMaximal I] 
--     : I • (⊤ : Submodule R M) = 0
--      → Module.length R M = Module.rank R⧸I M⧸(I • (⊤ : Submodule R M)) := by sorry

-- Use 10.52.5

-- Stacks Lemma 10.52.8: I is a finitely generated maximal ideal of R.
-- M is a finite R-mod and I^nM=0. Then length of M is finite.
lemma power_zero_finite_length [Ideal.IsMaximal I] (h₁ : Ideal.FG I) [Module.Finite R M]
    (h₂ : (∃ n : ℕ, (I ^ n) • (⊤ : Submodule R M) = 0)) :
     (∃ m : ℕ, Module.length R M ≤ m) := by sorry
    -- intro IisFG IisMaximal MisFinite power
    -- rcases power with ⟨n, npower⟩

open Finset

-- Stacks Lemma 10.53.3: R is Artinian iff R has finitely many maximal ideals
lemma Artinian_has_finite_max_ideal 
    [IsArtinianRing R] : Finite (MaximalSpectrum R) := by 
    by_contra infinite
    simp only [not_finite_iff_infinite] at infinite
    let m' : ℕ ↪ MaximalSpectrum R := Infinite.natEmbedding (MaximalSpectrum R)
    have m'inj := m'.injective
    let m'' : ℕ → Ideal R := fun n : ℕ ↦ ⨅ k ∈ range n, (m' k).asIdeal
    -- let f : ℕ → MaximalSpectrum R := fun n : ℕ ↦ m' n
    -- let F : (n : ℕ) → Fin n → MaximalSpectrum R := fun n k ↦ m' k
    have DCC : ∃ n : ℕ, ∀ k : ℕ, n ≤ k → m'' n = m'' k := by
      apply IsArtinian.monotone_stabilizes {
        toFun := m''
        monotone' := sorry
      }
    cases' DCC with n DCCn
    specialize DCCn (n+1)
    specialize DCCn (Nat.le_succ n)
    have containment1 : m'' n < (m' (n + 1)).asIdeal := by sorry
    have : ∀ (j : ℕ), (j ≠ n + 1) → ∃ x, x ∈ (m' j).asIdeal ∧ x ∉ (m' (n+1)).asIdeal := by
      intro j jnotn
      have notcontain : ¬ (m' j).asIdeal ≤ (m' (n+1)).asIdeal := by
        -- apply Ideal.IsMaximal (m' j).asIdeal
        sorry
      sorry
    sorry
      -- have distinct : (m' j).asIdeal ≠ (m' (n+1)).asIdeal := by         
      --   intro h
      --   apply Function.Injective.ne m'inj jnotn
      --   exact MaximalSpectrum.ext _ _ h      
      -- simp
      -- unfold 
     

-- Stacks Lemma 10.53.4: R Artinian => Jacobson ideal of R is nilpotent
-- This is in mathlib: IsArtinianRing.isNilpotent_jacobson_bot

-- Stacks Lemma 10.53.5: If R has finitely many maximal ideals and 
-- locally nilpotent Jacobson radical, then R is the product of its localizations at 
-- its maximal ideals. Also, all primes are maximal
abbrev Prod_of_localization :=
  Π I : MaximalSpectrum R, Localization.AtPrime I.1

-- instance : CommRing (Prod_of_localization R) := by
--   unfold Prod_of_localization
--   infer_instance
     
-- def foo : Prod_of_localization R →+* R where
--   toFun := sorry
--   -- invFun := sorry
--   --left_inv := sorry
--   --right_inv := sorry
--   map_mul' := sorry
--   map_add' := sorry

def product_of_localization_at_maximal_ideal [Finite (MaximalSpectrum R)]
    (h : Ideal.IsLocallyNilpotent (RingJacobson R)) :
    R ≃+* Prod_of_localization R := by sorry

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

-- Stacks Lemma 10.26.1 (Should already exists)
-- (1) The closure of a prime P is V(P)
-- (2) the irreducible closed subsets are V(P) for P prime
-- (3) the irreducible components are V(P) for P minimal prime
-- Lemma: X is an irreducible component of Spec(R) ↔ X = V(I) for I a minimal prime
lemma irred_comp_minmimal_prime (X) : 
    X ∈ irreducibleComponents (PrimeSpectrum R) 
      ↔ ∃ (P : minimalPrimes R), X = PrimeSpectrum.zeroLocus P := by
      sorry


-- Stacks Lemma 10.60.5: R is Artinian iff R is Noetherian of dimension 0
lemma Artinian_if_dim_le_zero_Noetherian (R : Type _) [CommRing R] : 
    IsNoetherianRing R ∧ Ideal.krullDim R ≤ 0 → IsArtinianRing R := by
    rintro ⟨RisNoetherian, dimzero⟩  
    rw [ring_Noetherian_iff_spec_Noetherian] at RisNoetherian
    have := fun X => (irred_comp_minmimal_prime R X).mp
    choose F hf using this
    let Z := irreducibleComponents (PrimeSpectrum R)
    -- have Zfinite : Set.Finite Z := by
      -- apply TopologicalSpace.NoetherianSpace.finite_irreducibleComponents ?_
      -- sorry
    --let P := fun 
    rw [← ring_Noetherian_iff_spec_Noetherian] at RisNoetherian
    have PrimeIsMaximal : ∀ X : Z, Ideal.IsMaximal (F X X.2).1 := by
      intro X
      have prime : Ideal.IsPrime (F X X.2).1 := (F X X.2).2.1.1
      rw [Ideal.dim_le_zero_iff] at dimzero
      exact dimzero ⟨_, prime⟩
    have JacLocallyNil : Ideal.IsLocallyNilpotent (RingJacobson R) := by sorry 
    let Loc := fun X : Z ↦ Localization.AtPrime (F X.1 X.2).1 
    have LocNoetherian : ∀ X, IsNoetherianRing (Loc X) := by 
      intro X
      sorry
      -- apply IsLocalization.isNoetherianRing (F X.1 X.2).1 (Loc X) RisNoetherian
    have Locdimzero : ∀ X, Ideal.krullDim (Loc X) ≤ 0 := by sorry
    have powerannihilates : ∀ X, ∃ n : ℕ, 
      ((F X.1 X.2).1) ^ n • (⊤: Submodule R (Loc X)) = 0 := by sorry
    have LocFinitelength : ∀ X, ∃ n : ℕ, Module.length R (Loc X) ≤ n := by
      intro X
      have idealfg : Ideal.FG (F X.1 X.2).1 := by
        rw [isNoetherianRing_iff_ideal_fg] at RisNoetherian
        specialize RisNoetherian (F X.1 X.2).1
        exact RisNoetherian
      have modulefg : Module.Finite R (Loc X) := by sorry -- this is wrong
      specialize PrimeIsMaximal X
      specialize powerannihilates X
      apply power_zero_finite_length R (F X.1 X.2).1 (Loc X) idealfg powerannihilates
    have RingFinitelength : ∃ n : ℕ, Module.length R R ≤ n := by sorry
    rw [IsArtinian_iff_finite_length]
    exact RingFinitelength

lemma dim_le_zero_Noetherian_if_Artinian (R : Type _) [CommRing R] : 
    IsArtinianRing R → IsNoetherianRing R ∧ Ideal.krullDim R ≤ 0 := by 
    intro RisArtinian
    constructor
    apply finite_length_is_Noetherian
    rwa [IsArtinian_iff_finite_length] at RisArtinian
    rw [Ideal.dim_le_zero_iff]
    intro I
    apply primes_of_Artinian_are_maximal















