import CommAlg.krull

variable {R : Type _} [CommRing R] (I : Ideal R)

open Ideal
open PrimeSpectrum

lemma comap_strictmono {𝔭 𝔮 : PrimeSpectrum (R ⧸ I)} (h : 𝔭 < 𝔮) :
  PrimeSpectrum.comap (Ideal.Quotient.mk I) 𝔭 < PrimeSpectrum.comap (Ideal.Quotient.mk I) 𝔮 := by
  rw [lt_iff_le_and_ne] at h ⊢
  refine' ⟨Ideal.comap_mono h.1, fun H => h.2 _⟩
  . apply PrimeSpectrum.comap_injective_of_surjective (Ideal.Quotient.mk I)
    . exact Quotient.mk_surjective
    . exact H

lemma ht_comap_eq_ht (𝔭 : PrimeSpectrum (R ⧸ I)) :
  height 𝔭 ≤ height (comap (Ideal.Quotient.mk I) 𝔭) := by
  rw [height, height, Set.chainHeight_le_chainHeight_iff]
  rintro l ⟨l_ch, l_lt⟩
  use l.map (comap <| Ideal.Quotient.mk I)
  refine' ⟨⟨_, _⟩, by simp⟩
  . apply List.chain'_map_of_chain' (PrimeSpectrum.comap (Ideal.Quotient.mk I)) _ l_ch
    intro a b hab; apply comap_strictmono; apply hab
  . rintro i hi
    rw [List.mem_map] at hi
    obtain ⟨a, a_mem, rfl⟩ := hi
    apply comap_strictmono
    apply l_lt a a_mem

/- TODO: find a better lemma to avoid repeated code -/
lemma dim_quotient_le_dim : krullDim (R ⧸ I) ≤ krullDim R := by
  by_cases H : Nontrivial (R ⧸ I)
  . obtain ⟨n, hn⟩ := krullDim_nonneg_of_nontrivial (R ⧸ I)
    rw [hn]
    induction' n using ENat.recTopCoe with n
    . have H := (krullDim_eq_top_iff _).mp hn
      show ⊤ ≤ _
      rw [top_le_iff, krullDim_eq_top_iff] 
      intro n
      obtain ⟨𝔭, hI⟩ := H n
      use comap (Ideal.Quotient.mk I) 𝔭
      apply le_trans hI (ht_comap_eq_ht I _)
    . show n ≤ krullDim _
      rw [le_krullDim_iff]
      obtain ⟨𝔭, hI⟩ := le_krullDim_iff.mp <| le_of_eq hn.symm
      use comap (Ideal.Quotient.mk I) 𝔭
      norm_cast at hI ⊢
      apply le_trans hI (ht_comap_eq_ht I _)
  . suffices : krullDim (R ⧸ I) = ⊥
    . rw [this]; apply bot_le
    rw [dim_eq_bot_iff, ←not_nontrivial_iff_subsingleton]
    exact H