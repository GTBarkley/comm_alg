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
import Mathlib.RingTheory.Artinian
import Mathlib.Algebra.Module.GradedModule
import Mathlib.RingTheory.Noetherian
import Mathlib.RingTheory.Finiteness
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.Order.Height
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.RingTheory.Ideal.LocalRing

-- Setting for "library_search"
set_option maxHeartbeats 0
macro "ls" : tactic => `(tactic|library_search)

-- New tactic "obviously"
macro "obviously" : tactic =>
  `(tactic| (
      first
        | dsimp; simp; done; dbg_trace "it was dsimp simp"
        | simp; done; dbg_trace "it was simp"
        | tauto; done; dbg_trace "it was tauto"
        | simp; tauto; done; dbg_trace "it was simp tauto"
        | rfl; done; dbg_trace "it was rfl"
        | norm_num; done; dbg_trace "it was norm_num"
        | /-change (@Eq ℝ _ _);-/ linarith; done; dbg_trace "it was linarith"
        -- | gcongr; done
        | ring; done; dbg_trace "it was ring"
        | trivial; done; dbg_trace "it was trivial"
        -- | nlinarith; done
        | fail "No, this is not obvious."))






-- @Definitions (to be classified)
section
open GradedMonoid.GSmul
open DirectSum

-- Definition of polynomail of type d 
def PolyType (f : ℤ → ℤ) (d : ℕ) := ∃ Poly : Polynomial ℚ, ∃ (N : ℤ), ∀ (n : ℤ), N ≤ n → f n = Polynomial.eval (n : ℚ) Poly ∧ d = Polynomial.degree Poly
noncomputable def length ( A : Type _) (M : Type _)
 [CommRing A] [AddCommGroup M] [Module A M] :=  Set.chainHeight {M' : Submodule A M | M' < ⊤}

-- Make instance of M_i being an R_0-module
instance tada1 (𝒜 : ℤ → Type _) (𝓜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (𝓜 i)]  [DirectSum.GCommRing 𝒜]
  [DirectSum.Gmodule 𝒜 𝓜] (i : ℤ ) : SMul (𝒜 0) (𝓜 i)
    where smul x y := @Eq.rec ℤ (0+i) (fun a _ => 𝓜 a) (GradedMonoid.GSmul.smul x y) i (zero_add i)

lemma mylem (𝒜 : ℤ → Type _) (𝓜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (𝓜 i)]  [DirectSum.GCommRing 𝒜]
  [h : DirectSum.Gmodule 𝒜 𝓜] (i : ℤ) (a : 𝒜 0) (m : 𝓜 i) :
  of _ _ (a • m) = of _ _ a • of _ _ m := by
  refine' Eq.trans _ (Gmodule.of_smul_of 𝒜 𝓜 a m).symm
  refine' of_eq_of_gradedMonoid_eq _
  exact Sigma.ext (zero_add _).symm <| eq_rec_heq _ _

instance tada2 (𝒜 : ℤ → Type _) (𝓜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (𝓜 i)]  [DirectSum.GCommRing 𝒜]
  [h : DirectSum.Gmodule 𝒜 𝓜] (i : ℤ ) : SMulWithZero (𝒜 0) (𝓜 i) := by
  letI := SMulWithZero.compHom (⨁ i, 𝓜 i) (of 𝒜 0).toZeroHom
  exact Function.Injective.smulWithZero (of 𝓜 i).toZeroHom Dfinsupp.single_injective (mylem 𝒜 𝓜 i)

instance tada3 (𝒜 : ℤ → Type _) (𝓜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (𝓜 i)]  [DirectSum.GCommRing 𝒜]
  [h : DirectSum.Gmodule 𝒜 𝓜] (i : ℤ ): Module (𝒜 0) (𝓜 i) := by
  letI := Module.compHom (⨁ j, 𝓜 j) (ofZeroRingHom 𝒜)
  exact Dfinsupp.single_injective.module (𝒜 0) (of 𝓜 i) (mylem 𝒜 𝓜 i)


-- Definition of a Hilbert function of a graded module
section
noncomputable def hilbert_function (𝒜 : ℤ → Type _) (𝓜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (𝓜 i)]
  [DirectSum.GCommRing 𝒜]
  [DirectSum.Gmodule 𝒜 𝓜] (hilb : ℤ → ℤ) := ∀ i, hilb i = (ENat.toNat (length (𝒜 0) (𝓜 i)))

noncomputable def dimensionring { A: Type _}
 [CommRing A] := krullDim (PrimeSpectrum A)

noncomputable def dimensionmodule ( A : Type _) (M : Type _)
 [CommRing A] [AddCommGroup M] [Module A M] := krullDim (PrimeSpectrum (A ⧸ ((⊤ : Submodule A M).annihilator)) )
end
--  lemma graded_local (𝒜 : ℤ → Type _) [SetLike (⨁ i, 𝒜 i)] (𝓜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (𝓜 i)]
--   [DirectSum.GCommRing 𝒜]
--   [DirectSum.Gmodule 𝒜 𝓜] (art: IsArtinianRing (𝒜 0)) (loc : LocalRing (𝒜 0)) : ∃ ( I : Ideal ((⨁ i, 𝒜 i))),(HomogeneousMax 𝒜 I) := sorry


-- Definition(s) of homogeneous ideals
def Ideal.IsHomogeneous' (𝒜 : ℤ → Type _) 
[∀ i, AddCommGroup (𝒜 i)] [DirectSum.GCommRing 𝒜] 
(I : Ideal (⨁ i, 𝒜 i)) := ∀ (i : ℤ ) 
⦃r : (⨁ i, 𝒜 i)⦄, r ∈ I → DirectSum.of _ i ( r i : 𝒜 i) ∈ I

def HomogeneousPrime (𝒜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [DirectSum.GCommRing 𝒜] (I : Ideal (⨁ i, 𝒜 i)):= (Ideal.IsPrime I) ∧ (Ideal.IsHomogeneous' 𝒜 I)
def HomogeneousMax (𝒜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [DirectSum.GCommRing 𝒜] (I : Ideal (⨁ i, 𝒜 i)):= (Ideal.IsMaximal I) ∧ (Ideal.IsHomogeneous' 𝒜 I)

--theorem monotone_stabilizes_iff_noetherian :
-- (∀ f : ℕ →o Submodule R M, ∃ n, ∀ m, n ≤ m → f n = f m) ↔ IsNoetherian R M := by
-- rw [isNoetherian_iff_wellFounded, WellFounded.monotone_chain_condition]


end










-- @[BH, 4.1.3] when d ≥ 1
-- If M is a finite graed R-Mod of dimension d ≥ 1, then the Hilbert function H(M, n) is of polynomial type (d - 1)
theorem hilbert_polynomial_ge1 (d : ℕ) (d1 : 1 ≤ d) (𝒜 : ℤ → Type _) (𝓜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (𝓜 i)]
[DirectSum.GCommRing 𝒜]
[DirectSum.Gmodule 𝒜 𝓜] (art: IsArtinianRing (𝒜 0)) (loc : LocalRing (𝒜 0)) 
(fingen : IsNoetherian (⨁ i, 𝒜 i) (⨁ i, 𝓜 i))
(findim :  dimensionmodule (⨁ i, 𝒜 i) (⨁ i, 𝓜 i) = d)
(hilb : ℤ → ℤ) (Hhilb: hilbert_function 𝒜 𝓜 hilb)
: PolyType hilb (d - 1) := by
  sorry




-- @[BH, 4.1.3] when d = 0
-- If M is a finite graed R-Mod of dimension zero, then the Hilbert function H(M, n) = 0 for n >> 0 
theorem hilbert_polynomial_0 (𝒜 : ℤ → Type _) (𝓜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (𝓜 i)]
[DirectSum.GCommRing 𝒜]
[DirectSum.Gmodule 𝒜 𝓜] (art: IsArtinianRing (𝒜 0)) (loc : LocalRing (𝒜 0)) 
(fingen : IsNoetherian (⨁ i, 𝒜 i) (⨁ i, 𝓜 i))
(findim :  dimensionmodule (⨁ i, 𝒜 i) (⨁ i, 𝓜 i) = 0)
(hilb : ℤ → ℤ) (Hhilb : hilbert_function 𝒜 𝓜 hilb)
: (∃ (N : ℤ), ∀ (n : ℤ), n ≥ N → hilb n = 0) := by
  sorry






-- @Existence of a chain of submodules of graded submoduels of a f.g graded R-mod M
lemma Exist_chain_of_graded_submodules (𝒜 : ℤ → Type _) (𝓜 : ℤ → Type _) 
[∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (𝓜 i)]
  [DirectSum.GCommRing 𝒜] [DirectSum.Gmodule 𝒜 𝓜] 
  (fingen : IsNoetherian (⨁ i, 𝒜 i) (⨁ i, 𝓜 i))
  : ∃ (c : List (Submodule (⨁ i, 𝒜 i) (⨁ i, 𝓜 i))), c.Chain' (· < ·) ∧ ∀ M ∈ c, Ture := by
  sorry





-- @[BH, 1.5.6 (b)(ii)]
-- An associated prime of a graded R-Mod M is graded
lemma Associated_prime_of_graded_is_graded
(𝒜 : ℤ → Type _) (𝓜 : ℤ → Type _) 
[∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (𝓜 i)]
[DirectSum.GCommRing 𝒜] [DirectSum.Gmodule 𝒜 𝓜]
(p : associatedPrimes (⨁ i, 𝒜 i) (⨁ i, 𝓜 i))
  : (Ideal.IsHomogeneous' 𝒜 p) ∧ ((∃ (i : ℤ ), ∃ (x :  𝒜 i), p = (Submodule.span (⨁ i, 𝒜 i) {DirectSum.of _ i x}).annihilator)) := by
  sorry


-- instance gyhoiu
-- (𝒜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [DirectSum.GCommRing 𝒜]
-- (p : Ideal (⨁ i, 𝒜 i)) (hp : Ideal.IsHomogeneous' 𝒜 p)
--   : (𝒫 : ℤ → Type _) [∀ i, AddCommGroup (𝒫 i)] [DirectSum.GCommRing 𝒫] → Gmodule (⊕ i, 𝒜 i)   := by
--   sorry


-- instance sdfasdf
-- (𝒜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [DirectSum.GCommRing 𝒜]
-- (p : Ideal (⨁ i, 𝒜 i)) (hp : Ideal.IsHomogeneous' 𝒜 p)
--   : ∀ i, AddCommGroup (p i) := by
--   sorry


def Component_of_graded_as_addsubgroup (𝒜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [DirectSum.GCommRing 𝒜]
(p : Ideal (⨁ i, 𝒜 i)) (hp : Ideal.IsHomogeneous' 𝒜 p) (i : ℤ) : AddSubgroup (𝒜 i) := sorry



-- @ Quotient of a graded ring R by a graded ideal p is a graded R-Mod, preserving each component
instance Quotient_of_graded_is_graded
(𝒜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [DirectSum.GCommRing 𝒜]
(p : Ideal (⨁ i, 𝒜 i)) (hp : Ideal.IsHomogeneous' 𝒜 p)
  : DirectSum.Gmodule 𝒜 (fun i => (𝒜 i)⧸(Component_of_graded_as_addsubgroup 𝒜 p hp i)) := by
  sorry

-- @Graded submodule

