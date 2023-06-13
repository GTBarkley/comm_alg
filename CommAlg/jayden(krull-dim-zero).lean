import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.JacobsonIdeal
import Mathlib.RingTheory.Noetherian
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Artinian
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.RingTheory.Nilpotent
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Maximal
import Mathlib.Data.Finite.Defs
import Mathlib.Order.Height
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.NoetherianSpace

-- copy from krull.lean; the name of Krull dimension for rings is changed to krullDim' since krullDim already exists in the librrary
namespace Ideal

variable (R : Type _) [CommRing R] (I : PrimeSpectrum R)

noncomputable def height : ℕ∞ := Set.chainHeight {J : PrimeSpectrum R | J < I}

noncomputable def krullDim' (R : Type) [CommRing R] : WithBot ℕ∞ := ⨆ (I : PrimeSpectrum R), height R I
-- copy ends

-- Stacks Lemma 10.60.5: R is Artinian iff R is Noetherian of dimension 0
lemma dim_zero_Noetherian_iff_Artinian (R : Type _) [CommRing R] : 
    IsNoetherianRing R ∧ krullDim' R = 0 ↔ IsArtinianRing R := by sorry


#check IsNoetherianRing

#check krullDim

-- Repeats the definition of the length of a module by Monalisa
variable (M : Type _) [AddCommMonoid M] [Module R M]

-- change the definition of length
noncomputable def length := Set.chainHeight {M' : Submodule R M | M' < ⊤}

#check length
-- Stacks Lemma 10.53.6: R is Artinian iff R has finite length as an R-mod
lemma IsArtinian_iff_finite_length : IsArtinianRing R ↔ ∃ n : ℕ, length R R ≤ n := by sorry 

-- Stacks Lemma 10.53.3: R is Artinian iff R has finitely many maximal ideals
lemma IsArtinian_iff_finite_max_ideal : IsArtinianRing R ↔ Finite (MaximalSpectrum R) := by sorry

-- Stacks Lemma 10.53.4: R Artinian => Jacobson ideal of R is nilpotent
lemma Jacobson_of_Artinian_is_nilpotent : IsArtinianRing R → IsNilpotent (Ideal.jacobson (⊤ : Ideal R)) := by sorry


-- Stacks Definition 10.32.1: An ideal is locally nilpotent
-- if every element is nilpotent
namespace Ideal
class IsLocallyNilpotent (I : Ideal R) : Prop :=
    h : ∀ x ∈ I, IsNilpotent x

end Ideal

#check Ideal.IsLocallyNilpotent

-- Stacks Lemma 10.53.5: If R has finitely many maximal ideals and 
-- locally nilpotent Jacobson radical, then R is the product of its localizations at 
-- its maximal ideals. Also, all primes are maximal

lemma product_of_localization_at_maximal_ideal : Finite (MaximalSpectrum R)
     ∧ Ideal.IsLocallyNilpotent (Ideal.jacobson (⊤ : Ideal R)) → Pi.commRing (MaximalSpectrum R) Localization.AtPrime R I
      := by sorry
-- Haven't finished this.

-- Stacks Lemma 10.31.5: R is Noetherian iff Spec(R) is a Noetherian space
lemma ring_Noetherian_iff_spec_Noetherian : IsNoetherianRing R 
    ↔ TopologicalSpace.NoetherianSpace (PrimeSpectrum R) := by sorry
-- Use TopologicalSpace.NoetherianSpace.exists_finset_irreducible :
-- Every closed subset of a noetherian space is a finite union 
-- of irreducible closed subsets.


-- Stacks Lemma 10.26.1 (Should already exists)
-- (1) The closure of a prime P is V(P)
-- (2) the irreducible closed subsets are V(P) for P prime
-- (3) the irreducible components are V(P) for P minimal prime

-- Stacks Lemma 10.32.5: R Noetherian. I,J ideals. If J ⊂ √I, then J ^ n ⊂ I for some n  

-- how to use namespace

namespace something

end something

open something






