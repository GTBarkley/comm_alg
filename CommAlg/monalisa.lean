import Mathlib.Order.KrullDimension
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Algebra.Module.GradedModule
import Mathlib.RingTheory.Ideal.AssociatedPrime
import Mathlib.RingTheory.Artinian
import Mathlib.Order.Height
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.FiniteType

noncomputable def length ( A : Type _) (M : Type _)
 [CommRing A] [AddCommGroup M] [Module A M] :=  Set.chainHeight {M' : Submodule A M | M' < ⊤}

 def Ideal.IsHomogeneous' (𝒜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)]
  [DirectSum.GCommRing 𝒜] (I : Ideal (⨁ i, 𝒜 i)) := ∀ (i : ℤ ) ⦃r : (⨁ i, 𝒜 i)⦄, r ∈ I → DirectSum.of _ i ( r i : 𝒜 i) ∈ I 


def HomogeneousPrime (𝒜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [DirectSum.GCommRing 𝒜] (I : Ideal (⨁ i, 𝒜 i)):= (Ideal.IsPrime I) ∧ (Ideal.IsHomogeneous' 𝒜 I)


def HomogeneousMax (𝒜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [DirectSum.GCommRing 𝒜] (I : Ideal (⨁ i, 𝒜 i)):= (Ideal.IsMaximal I) ∧ (Ideal.IsHomogeneous' 𝒜 I)

--theorem monotone_stabilizes_iff_noetherian :
-- (∀ f : ℕ →o Submodule R M, ∃ n, ∀ m, n ≤ m → f n = f m) ↔ IsNoetherian R M := by
-- rw [isNoetherian_iff_wellFounded, WellFounded.monotone_chain_condition]

open GradedMonoid.GSmul

open DirectSum


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

noncomputable def hilbert_function (𝒜 : ℤ → Type _) (𝓜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (𝓜 i)]
  [DirectSum.GCommRing 𝒜]
  [DirectSum.Gmodule 𝒜 𝓜] (hilb : ℤ → ℤ) := ∀ i, hilb i = (ENat.toNat (length (𝒜 0) (𝓜 i)))

noncomputable def dimensionring { A: Type _}
 [CommRing A] := krullDim (PrimeSpectrum A)


noncomputable def dimensionmodule ( A : Type _) (M : Type _)
 [CommRing A] [AddCommGroup M] [Module A M] := krullDim (PrimeSpectrum (A ⧸ ((⊤ : Submodule A M).annihilator)) )

-- (∃ (i : ℤ ), ∃ (x :  𝒜 i), p = (Submodule.span (⨁ i, 𝒜 i) {x}).annihilator ) 

--  lemma graded_local (𝒜 : ℤ → Type _) [SetLike (⨁ i, 𝒜 i)] (𝓜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (𝓜 i)]
--   [DirectSum.GCommRing 𝒜]
--   [DirectSum.Gmodule 𝒜 𝓜] (art: IsArtinianRing (𝒜 0)) (loc : LocalRing (𝒜 0)) : ∃ ( I : Ideal ((⨁ i, 𝒜 i))),(HomogeneousMax 𝒜 I) := sorry


def PolyType (f : ℤ → ℤ) (d : ℕ  ) := ∃ Poly : Polynomial ℚ, ∃ (N : ℤ), ∀ (n : ℤ), N ≤ n → f n = Polynomial.eval (n : ℚ) Poly ∧ d = Polynomial.degree Poly



theorem hilbert_polynomial (d : ℕ) (d1 : 1 ≤ d) (𝒜 : ℤ → Type _) (𝓜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (𝓜 i)]
[DirectSum.GCommRing 𝒜]
[DirectSum.Gmodule 𝒜 𝓜] (art: IsArtinianRing (𝒜 0)) (loc : LocalRing (𝒜 0)) 
(fingen : IsNoetherian (⨁ i, 𝒜 i) (⨁ i, 𝓜 i))
(findim :  dimensionmodule (⨁ i, 𝒜 i) (⨁ i, 𝓜 i) = d) (hilb : ℤ → ℤ)
 (Hhilb: hilbert_function 𝒜 𝓜 hilb)
: PolyType hilb (d - 1) := by
  sorry


theorem hilbert_polynomial_0 (𝒜 : ℤ → Type _) (𝓜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (𝓜 i)]
[DirectSum.GCommRing 𝒜]
[DirectSum.Gmodule 𝒜 𝓜] (art: IsArtinianRing (𝒜 0)) (loc : LocalRing (𝒜 0)) 
(fingen : IsNoetherian (⨁ i, 𝒜 i) (⨁ i, 𝓜 i))
(findim :  dimensionmodule (⨁ i, 𝒜 i) (⨁ i, 𝓜 i) = 0) (hilb : ℤ → ℤ)
: true := by
  sorry

lemma Associated_prime_of_graded_is_graded
(𝒜 : ℤ → Type _) (𝓜 : ℤ → Type _) 
[∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (𝓜 i)]
[DirectSum.GCommRing 𝒜] [DirectSum.Gmodule 𝒜 𝓜]
(p : associatedPrimes (⨁ i, 𝒜 i) (⨁ i, 𝓜 i))
  : (Ideal.IsHomogeneous' 𝒜 p) ∧ ((∃ (i : ℤ ), ∃ (x :  𝒜 i), p = (Submodule.span (⨁ i, 𝒜 i) {DirectSum.of _ i x}).annihilator)) := by
  sorry


-- def standard_graded {𝒜 : ℤ → Type _} [∀ i, AddCommGroup (𝒜 i)] [DirectSum.GCommRing 𝒜] (n : ℕ) :
--     Prop :=
--   ∃ J, Ideal.IsHomogeneous' 𝒜 J (J :Nonempty ((⨁ i, 𝒜 i) ≃+* (MvPolynomial (Fin n) (𝒜 0)) ⧸ J)
