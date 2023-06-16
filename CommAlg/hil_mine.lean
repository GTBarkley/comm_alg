import CommAlg.final_hil_pol
import Mathlib.Algebra.Ring.Defs

set_option maxHeartbeats 0



theorem Hilbert_polynomial_d_0_reduced
(𝒜 : ℤ → Type _) [∀ i, AddCommGroup (𝒜 i)] 
[DirectSum.GCommRing 𝒜][LocalRing (𝒜 0)] [StandardGraded 𝒜] (art: IsArtinianRing (𝒜 0)) (p : Ideal (⨁ i, 𝒜 i)) (hp : Ideal.IsHomogeneous' 𝒜 p)
(fingen : IsNoetherian (⨁ i, 𝒜 i) (⨁ i, (𝒜 i)⧸(Component_of_graded_as_addsubgroup 𝒜 p hp i)))
(findim :  dimensionmodule (⨁ i, 𝒜 i) (⨁ i, (𝒜 i)⧸(Component_of_graded_as_addsubgroup 𝒜 p hp i)) = 0)
(hilb : ℤ → ℤ) (Hhilb : hilbert_function 𝒜 (fun i => (𝒜 i)⧸(Component_of_graded_as_addsubgroup 𝒜 p hp i)) hilb)
 (hq : HomogeneousPrime 𝒜 p) (n : ℤ) (n_0 : 0 < n)
: hilb n = 0 := by 
  have h1 : dimensionmodule (⨁ i, 𝒜 i) ((⨁ i, (𝒜 i))⧸p) = dimensionmodule (⨁ i, 𝒜 i) (⨁ i, ((𝒜 i)⧸(Component_of_graded_as_addsubgroup 𝒜 p hp i))) := by 
    apply dim_iso (⨁ i, 𝒜 i) ((⨁ i, (𝒜 i))⧸p) (⨁ i, ((𝒜 i)⧸(Component_of_graded_as_addsubgroup 𝒜 p hp i)))
    exact Quotient_of_graded_ringiso 𝒜 p hp
  have h2 : dimensionmodule (⨁ i, 𝒜 i) ((⨁ i, (𝒜 i))⧸p) = Ideal.krullDim ((⨁ i, (𝒜 i))⧸p) := by 
    apply equaldim (⨁ i, 𝒜 i) p
  have h3 : 0 = Ideal.krullDim ((⨁ i, 𝒜 i) ⧸ p) := by   
    calc 0 = dimensionmodule (⨁ i, 𝒜 i) (⨁ i, ((𝒜 i)⧸(Component_of_graded_as_addsubgroup 𝒜 p hp i))) := findim.symm
         _ = dimensionmodule (⨁ i, 𝒜 i) ((⨁ i, (𝒜 i))⧸p) := h1.symm
         _ = Ideal.krullDim ((⨁ i, (𝒜 i))⧸p) :=  h2
  have h4 : IsDomain ((⨁ i, (𝒜 i))⧸p) := (Ideal.Quotient.isDomain_iff_prime p).mpr hq.1
  have h5 : IsField ((⨁ i, (𝒜 i))⧸p) := Ideal.domain_dim_zero.isField (h3.symm)
  have h6 : p.IsMaximal := Ideal.Quotient.maximal_of_isField p h5
  have h7 : HomogeneousMax 𝒜 p := ⟨h6, hq.2⟩
  -- have h8 : Nonempty ((⨁ i, 𝒜 i)⧸ p  →+* (𝒜 0)⧸(LocalRing.maximalIdeal (𝒜 0))) := Graded_local 𝒜 p h7 art
  -- set m := LocalRing.maximalIdeal (𝒜 0)
  -- have h0 : m.IsMaximal := LocalRing.maximalIdeal.isMaximal (𝒜 0)
  -- have h9 : IsField ((𝒜 0)⧸m) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient m).mp h0
  -- set k := ((𝒜 0)⧸m)
  -- have hilb n 
  sorry

  
  

