import Mathlib.Order.KrullDimension
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Algebra.Module.GradedModule
import Mathlib.RingTheory.Ideal.AssociatedPrime
import Mathlib.RingTheory.Artinian
import Mathlib.Order.Height
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.RingTheory.SimpleModule
import CommAlg.krull


#check Ideal.dim_field_eq_zero
#check Ideal.domain_dim_zero.isField
#check Ideal.Quotient.isDomain_iff_prime


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



open GradedMonoid.GSmul
open DirectSum



-- @Definitions (to be classified)
section

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

noncomputable def dimensionmodule ( A : Type _) (M : Type _)
 [CommRing A] [AddCommGroup M] [Module A M] := Ideal.krullDim  (A ⧸ ((⊤ : Submodule A M).annihilator)) 


lemma equaldim ( A : Type _) [CommRing A] (I : Ideal A): dimensionmodule (A) (A ⧸ I) = Ideal.krullDim (A ⧸ I) := by
sorry
end



-- Definition of homogeneous ideal
def Ideal.IsHomogeneous' (𝒜 : ℤ → Type _) 
[∀ i, AddCommGroup (𝒜 i)] [DirectSum.GCommRing 𝒜] 
(I : Ideal (⨁ i, 𝒜 i)) := ∀ (i : ℤ ) 
⦃r : (⨁ i, 𝒜 i)⦄, r ∈ I → DirectSum.of _ i ( r i : 𝒜 i) ∈ I

-- Definition of homogeneous prime ideal
def HomogeneousPrime (𝒜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [DirectSum.GCommRing 𝒜] (I : Ideal (⨁ i, 𝒜 i)):= (Ideal.IsPrime I) ∧ (Ideal.IsHomogeneous' 𝒜 I)

-- Definition of homogeneous maximal ideal
def HomogeneousMax (𝒜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [DirectSum.GCommRing 𝒜] (I : Ideal (⨁ i, 𝒜 i)):= (Ideal.IsMaximal I) ∧ (Ideal.IsHomogeneous' 𝒜 I)

--theorem monotone_stabilizes_iff_noetherian :
-- (∀ f : ℕ →o Submodule R M, ∃ n, ∀ m, n ≤ m → f n = f m) ↔ IsNoetherian R M := by
-- rw [isNoetherian_iff_wellFounded, WellFounded.monotone_chain_condition]


instance {𝒜 : ℤ → Type _} [∀ i, AddCommGroup (𝒜 i)] [DirectSum.GCommRing 𝒜] :
    Algebra (𝒜 0) (⨁ i, 𝒜 i) :=
  Algebra.ofModule'
  (by
    intro r x
    sorry)
  (by
    intro r x
    sorry)



class StandardGraded (𝒜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [DirectSum.GCommRing 𝒜] : Prop where
  gen_in_first_piece :
    Algebra.adjoin (𝒜 0) (DirectSum.of _ 1 : 𝒜 1 →+ ⨁ i, 𝒜 i).range = (⊤ : Subalgebra (𝒜 0) (⨁ i, 𝒜 i))


-- Each component of a graded ring is an additive subgroup
def Component_of_graded_as_addsubgroup (𝒜 : ℤ → Type _) 
[∀ i, AddCommGroup (𝒜 i)] [DirectSum.GCommRing 𝒜]
(p : Ideal (⨁ i, 𝒜 i)) (hp : Ideal.IsHomogeneous' 𝒜 p) (i : ℤ) : AddSubgroup (𝒜 i) := by
  sorry


def graded_ring_morphism (𝒜 : ℤ → Type _) (ℬ : ℤ → Type _)
[∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (ℬ i)]
[DirectSum.GCommRing 𝒜] [DirectSum.GCommRing ℬ] (f : (⨁ i, 𝒜 i) →+* (⨁ i, ℬ i)) := ∀ i, ∀ (r : 𝒜 i), ∀ j, (j ≠ i → f (DirectSum.of _ i r) j = 0)

def graded_module_morphism (𝒜 : ℤ → Type _) (𝓜 : ℤ → Type _) (𝓝 : ℤ → Type _)
[∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (𝓜 i)] [∀ i, AddCommGroup (𝓝 i)]
[DirectSum.GCommRing 𝒜] [DirectSum.Gmodule 𝒜 𝓜][DirectSum.Gmodule 𝒜 𝓝] (f : (⨁ i, 𝓜 i) → (⨁ i, 𝓝 i)) := ∀ i, ∀ (r : 𝓜 i), ∀ j, (j ≠ i → f (DirectSum.of _ i r) j = 0) ∧ (IsLinearMap (⨁ i, 𝒜 i) f)

def graded_module_isomorphism (𝒜 : ℤ → Type _) (𝓜 : ℤ → Type _) (𝓝 : ℤ → Type _)
[∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (𝓜 i)] [∀ i, AddCommGroup (𝓝 i)]
[DirectSum.GCommRing 𝒜] [DirectSum.Gmodule 𝒜 𝓜][DirectSum.Gmodule 𝒜 𝓝]
(f : (⨁ i, 𝓜 i) →  (⨁ i, 𝓝 i))
:= (graded_module_morphism 𝒜 𝓜 𝓝 f) ∧ (Function.Bijective f)

def graded_ring_isomorphism (𝒜 : ℤ → Type _) (𝓑 : ℤ → Type _)
[∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (𝓑 i)]
[DirectSum.GCommRing 𝒜] [DirectSum.GCommRing 𝓑]
(f : (⨁ i, 𝒜 i) →+*  (⨁ i, 𝓑 i))
:= (graded_ring_morphism 𝒜 𝓑 f) ∧ (Function.Bijective f)

def graded_ring_isomorphic (𝒜 : ℤ → Type _) (𝓑 : ℤ → Type _)
[∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (𝓑 i)]
[DirectSum.GCommRing 𝒜] [DirectSum.GCommRing 𝓑] := ∃ (f : (⨁ i, 𝒜 i) →+*  (⨁ i, 𝓑 i)),graded_ring_isomorphism 𝒜 𝓑 f



-- def graded_submodule
--     (𝒜 : ℤ → Type _) (𝓜 : ℤ → Type _) (𝓝 : ℤ → Type _)
--     [∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (𝓜 i)] [∀ i, AddCommGroup (𝓝 i)]
--     [DirectSum.GCommRing 𝒜] [DirectSum.Gmodule 𝒜 𝓜][DirectSum.Gmodule 𝒜 𝓝]
--     (h (⨁ i, 𝓝 i) : Submodule (⨁ i, 𝒜 i) (⨁ i, 𝓜 i)) :
--     Prop :=
--   ∃ (piece : Submodule (𝒜 0) (𝓜 i)), piece = 𝓝 i


end

class DirectSum.GalgebrA
  (𝒜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [DirectSum.GCommRing 𝒜]
  (𝓜 : ℤ → Type _) [∀ i, AddCommGroup (𝓜 i)] [DirectSum.GCommRing 𝓜]
  extends DirectSum.Gmodule 𝒜 𝓜

def graded_algebra_morphism (𝒜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [DirectSum.GCommRing 𝒜]
  (𝓜 : ℤ → Type _) [∀ i, AddCommGroup (𝓜 i)] [DirectSum.GCommRing 𝓜] [DirectSum.GalgebrA 𝒜 𝓜]
  (𝓝 : ℤ → Type _) [∀ i, AddCommGroup (𝓝 i)] [DirectSum.GCommRing 𝓝] [DirectSum.GalgebrA 𝒜 𝓝] 
  (f : (⨁ i, 𝓜 i) →+*  (⨁ i, 𝓝 i)) := (graded_ring_morphism 𝓜 𝓝 f) ∧ (graded_module_morphism 𝒜 𝓜 𝓝 f)  



-- @Quotient of a graded ring R by a graded ideal p is a graded R-alg, preserving each component

instance Quotient_of_graded_gradedring
(𝒜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [DirectSum.GCommRing 𝒜]
(p : Ideal (⨁ i, 𝒜 i)) (hp : Ideal.IsHomogeneous' 𝒜 p)
  : DirectSum.GCommRing (fun i => (𝒜 i)⧸(Component_of_graded_as_addsubgroup 𝒜 p hp i)) := by
  sorry

instance Quotient_of_graded_is_gradedalg
(𝒜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [DirectSum.GCommRing 𝒜]
(p : Ideal (⨁ i, 𝒜 i)) (hp : Ideal.IsHomogeneous' 𝒜 p)
  : DirectSum.GalgebrA 𝒜 (fun i => (𝒜 i)⧸(Component_of_graded_as_addsubgroup 𝒜 p hp i)) := by
  sorry

lemma Quotient_of_graded_ringiso (𝒜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [DirectSum.GCommRing 𝒜](p : Ideal (⨁ i, 𝒜 i)) (hp : Ideal.IsHomogeneous' 𝒜 p)
(hm : 𝓜 = (fun i => (𝒜 i)⧸(Component_of_graded_as_addsubgroup 𝒜 p hp i)))
: Nonempty ((⨁ i, (𝒜 i)⧸(Component_of_graded_as_addsubgroup 𝒜 p hp i)) ≃+*  ((⨁ i, (𝒜 i))⧸p)) := by
  sorry


-- If A_0 is Artinian and local, then A is graded local
lemma Graded_local_if_zero_component_Artinian_and_local (𝒜 : ℤ → Type _) (𝓜 : ℤ → Type _) 
[∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (𝓜 i)]
[DirectSum.GCommRing 𝒜] [DirectSum.Gmodule 𝒜 𝓜] (art: IsArtinianRing (𝒜 0)) (loc : LocalRing (𝒜 0)) : ∃! ( I : Ideal ((⨁ i, 𝒜 i))),(HomogeneousMax 𝒜 I) := by
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









-- @[BH, 4.1.3] when d ≥ 1
-- If M is a finite graed R-Mod of dimension d ≥ 1, then the Hilbert function H(M, n) is of polynomial type (d - 1)
theorem Hilbert_polynomial_d_ge_1 (d : ℕ) (d1 : 1 ≤ d) (𝒜 : ℤ → Type _) (𝓜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (𝓜 i)]
[DirectSum.GCommRing 𝒜]
[DirectSum.Gmodule 𝒜 𝓜] (st: StandardGraded 𝒜) (art: IsArtinianRing (𝒜 0)) (loc : LocalRing (𝒜 0)) 
(fingen : IsNoetherian (⨁ i, 𝒜 i) (⨁ i, 𝓜 i))
(findim :  dimensionmodule (⨁ i, 𝒜 i) (⨁ i, 𝓜 i) = d)
(hilb : ℤ → ℤ) (Hhilb: hilbert_function 𝒜 𝓜 hilb)

: PolyType hilb (d - 1) := by
  sorry


-- (reduced version) [BH, 4.1.3] when d ≥ 1
-- If M is a finite graed R-Mod of dimension d ≥ 1, and M = R⧸ 𝓅 for a graded prime ideal 𝓅, then the Hilbert function H(M, n) is of polynomial type (d - 1)
theorem Hilbert_polynomial_d_ge_1_reduced 
(d : ℕ) (d1 : 1 ≤ d)
(𝒜 : ℤ → Type _) (𝓜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (𝓜 i)]
[DirectSum.GCommRing 𝒜]
[DirectSum.Gmodule 𝒜 𝓜] (st: StandardGraded 𝒜) (art: IsArtinianRing (𝒜 0)) (loc : LocalRing (𝒜 0))
(fingen : IsNoetherian (⨁ i, 𝒜 i) (⨁ i, 𝓜 i))
(findim :  dimensionmodule (⨁ i, 𝒜 i) (⨁ i, 𝓜 i) = d)
(hilb : ℤ → ℤ) (Hhilb: hilbert_function 𝒜 𝓜 hilb)
(p : Ideal (⨁ i, 𝒜 i)) (hp : Ideal.IsHomogeneous' 𝒜 p)
(hm : 𝓜 = (fun i => (𝒜 i)⧸(Component_of_graded_as_addsubgroup 𝒜 p hp i)))
: PolyType hilb (d - 1) := by
  sorry


-- @[BH, 4.1.3] when d = 0
-- If M is a finite graed R-Mod of dimension zero, then the Hilbert function H(M, n) = 0 for n >> 0 
theorem Hilbert_polynomial_d_0 (𝒜 : ℤ → Type _) (𝓜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (𝓜 i)]
[DirectSum.GCommRing 𝒜]
[DirectSum.Gmodule 𝒜 𝓜] (st: StandardGraded 𝒜) (art: IsArtinianRing (𝒜 0)) (loc : LocalRing (𝒜 0)) 
(fingen : IsNoetherian (⨁ i, 𝒜 i) (⨁ i, 𝓜 i))
(findim :  dimensionmodule (⨁ i, 𝒜 i) (⨁ i, 𝓜 i) = 0)
(hilb : ℤ → ℤ) (Hhilb : hilbert_function 𝒜 𝓜 hilb)
: (∃ (N : ℤ), ∀ (n : ℤ), n ≥ N → hilb n = 0) := by
  sorry


#check Ideal.dim_field_eq_zero
#check Ideal.domain_dim_zero.isField
--#check Quotient.isDomain_iff_prime

#check DirectSum

-- f (g a) = f (g b)

-- DirectSum _ (fun i => ...) = DirectSum _ (fun i => ...)

theorem Hilbert_polynomial_d_0_reduced
(𝒜 : ℤ → Type _) (𝓜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (𝓜 i)]
[DirectSum.GCommRing 𝒜] [DirectSum.GCommRing 𝓜]
[DirectSum.GalgebrA 𝒜 𝓜] (st: StandardGraded 𝒜) (art: IsArtinianRing (𝒜 0)) (loc : LocalRing (𝒜 0)) 
(fingen : IsNoetherian (⨁ i, 𝒜 i) (⨁ i, 𝓜 i))
(findim :  dimensionmodule (⨁ i, 𝒜 i) (⨁ i, 𝓜 i) = 0)
(hilb : ℤ → ℤ) (Hhilb : hilbert_function 𝒜 𝓜 hilb)
(p : Ideal (⨁ i, 𝒜 i)) (hp : Ideal.IsHomogeneous' 𝒜 p) (hq : HomogeneousPrime 𝒜 p)
(hm : ∀ i, 𝓜 i = ((𝒜 i)⧸(Component_of_graded_as_addsubgroup 𝒜 p hp i)))
: (∃ (N : ℤ), ∀ (n : ℤ), n ≥ N → hilb n = 0) := by 
  let 𝓜' := fun i => (𝒜 i)⧸(Component_of_graded_as_addsubgroup 𝒜 p hp i)
  have h : 𝓜 = 𝓜' := by
    ext i
    exact hm i
  subst h
  set R := ⨁ i, 𝒜 i
  have : (⨁ i, 𝓜' i )= ⨁ i, ((𝒜 i)⧸(Component_of_graded_as_addsubgroup 𝒜 p hp i)) := by
    rfl
  
--have h1 : Nonempty ((⨁ i, 𝓜 i) ≃+*  (R⧸p)) := by 

--   apply Quotient_of_graded_ringiso 𝒜 p hp
--  have : Ideal.krullDim (R ⧸ p) = 0 := by   
--    calc 0 = dimensionmodule (⨁ i, 𝒜 i) (⨁ i, 𝓜 i) := by apply findim
--        _ = dimensionmodule (R) (R ⧸ p) := by apply h1
--        _ = Ideal.krullDim (R_mod_p) := by apply equaldim
-- sorry

lemma   

-- (reduced version) [BH, 4.1.3] when d = 0
-- If M is a finite graed R-Mod of dimension zero, and M = R⧸ 𝓅 for a graded prime ideal 𝓅, then the Hilbert function H(M, n) = 0 for n >> 0 
-- theorem Hilbert_polynomial_d_0_reduced
-- (𝒜 : ℤ → Type _) (𝓜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (𝓜 i)]
-- [DirectSum.GCommRing 𝒜] [DirectSum.GCommRing 𝓜]
-- [DirectSum.GalgebrA 𝒜 𝓜] (st: StandardGraded 𝒜) (art: IsArtinianRing (𝒜 0)) (loc : LocalRing (𝒜 0)) 
-- (fingen : IsNoetherian (⨁ i, 𝒜 i) (⨁ i, 𝓜 i))
-- (findim :  dimensionmodule (⨁ i, 𝒜 i) (⨁ i, 𝓜 i) = 0)
-- (hilb : ℤ → ℤ) (Hhilb : hilbert_function 𝒜 𝓜 hilb)
-- (p : Ideal (⨁ i, 𝒜 i)) (hp : Ideal.IsHomogeneous' 𝒜 p) (hq : HomogeneousPrime 𝒜 p)
-- (hm : 𝓜 = (fun i => (𝒜 i)⧸(Component_of_graded_as_addsubgroup 𝒜 p hp i)))
-- : (∃ (N : ℤ), ∀ (n : ℤ), n ≥ N → hilb n = 0) := by 
-- set R := ⨁ i, 𝒜 i
-- have h := (Ideal.Quotient.isDomain_iff_prime p).mpr hq.1
-- have h1 : Nonempty ((⨁ i, 𝓜 i)) ≃+*  (R⧸p)) := by 
--   apply Quotient_of_graded_ringiso 𝒜 p hp
--  have : Ideal.krullDim (R ⧸ p) = 0 := by   
--    calc 0 = dimensionmodule (⨁ i, 𝒜 i) (⨁ i, 𝓜 i) := by apply findim
--        _ = dimensionmodule (R) (R ⧸ p) := by apply h1
--        _ = Ideal.krullDim (R_mod_p) := by apply equaldim
-- sorry


















