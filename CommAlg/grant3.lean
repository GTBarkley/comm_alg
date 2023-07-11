import Mathlib.Data.Nat.Lattice
import Mathlib.Data.ENat.Lattice
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Order.CompleteLattice
import Mathlib.Order.WithBot
import Mathlib.Order.Height
import CommAlg.StrictSeries
import Mathlib.Tactic.TFAE


noncomputable def chainLength (α : Type _) [LT α] : WithBot ℕ∞ := ⨆ (s : StrictSeries α), s.length

noncomputable def height {α : Type _} [LT α] (x : α) : ℕ∞ := ⨆ s ∈ {s : StrictSeries α | s.top = x}, s.length

noncomputable def krullDim (R : Type _) [CommRing R] : WithBot ℕ∞ := chainLength (PrimeSpectrum R)

lemma krullDim_def (R : Type _) [CommRing R] : krullDim R = (⨆ (I : PrimeSpectrum R), height I : WithBot ℕ∞) := sorry
lemma krullDim_def' (R : Type _) [CommRing R] : krullDim R = iSup (λ I : PrimeSpectrum R => (height I : WithBot ℕ∞)) := sorry

variable {α : Type _} [LT α]

lemma height_eq_chainHeight (p : α) : height p = Set.chainHeight {J : α | J < p} := sorry

lemma chainLength_eq_bot : chainLength α = ⊥ ↔ IsEmpty α := by
  sorry

lemma chainLength_eq_sup_height : chainLength α = ⨆ p : α, (height p : WithBot ℕ∞) := by
  cases' isEmpty_or_nonempty α
  . simp [chainLength]
  . show (⨆ (s : _), ((_ : ℕ∞) : WithBot ℕ∞)) = _
    norm_cast
    unfold height
    rw [iSup_comm]
    apply le_antisymm <;> simp [iSup_mono]

#synth (IsWellOrder (WithBot ℕ∞) (·<·))
#check le_iSup

theorem lt_height_TFAE (p : α) (n : ℕ∞) :
List.TFAE [n < height p, ∃ c : StrictSeries α, c.top = p ∧ c.length > n, ∃c : StrictSeries α, c.top = p ∧ c.length = n + 1] := by
  cases' n using ENat.recTopCoe with n
  . tfae_have 1 ↔ 2; simp
    tfae_have 1 ↔ 3; simp
    tfae_finish
  . norm_cast
    sorry
    -- tfae_have 1 → 2
    -- . sorry
    -- tfae_have 2 → 3
    -- . sorry
    -- tfae_have 3 → 1
    -- . sorry 
    -- tfae_finish
  
theorem lt_height_iff {p : α} {n : ℕ∞} :
n < height p ↔ ∃ c : StrictSeries α, c.top = p ∧ c.length = n + 1 := 
  lt_height_TFAE p n |>.out 0 2

theorem le_height_iff {p : α} {n : ℕ} :
n ≤ height p ↔ ∃ c : StrictSeries α, c.top = p ∧ c.length = n :=
  match n with
  | 0 => ⟨fun _ => ⟨StrictSeries.ofElement p, by simp⟩, by simp⟩
  | n + 1 => by
    erw [(ENat.add_one_le_iff <| ENat.coe_ne_top _), lt_height_iff]
    norm_cast
  -- unfold height
  -- constructor <;> intro h
  -- . 
  --   -- cases' isEmpty_or_nonempty α
  --   -- . exfalso; exact IsEmpty.false p
  --   by_cases case : ∃ (c : StrictSeries α) (hc : c.top = p), n ≤ c.length
  --   . sorry
  --   -- generalize hj : (⨆ (_), (_ : ℕ∞)) = j at h
  --   -- have : ∃ (c : StrictSeries α) (hc : c.top = p), n ≤ c.length := by
  --   --   induction' j using ENat.recTopCoe with j
  --   --   . simp at hj
  --   --     sorry
  --   --   . norm_cast at h
  --   --     sorry
  --   . push_neg at case
  --     have : 0 < n := by
  --       let c := StrictSeries.ofList [p] (List.cons_ne_nil _ _) (List.chain'_singleton p)
  --       specialize case c (by rw [])
  --       simp
  --       sorry
  --     sorry
  -- . rcases h with ⟨c, hc⟩
  --   exact (hc.2 ▸ le_iSup₂ (f := fun (x : StrictSeries α) _ => (x.length : ℕ∞)) c) hc.1

theorem lt_height_iff'' {p : α} {n : ℕ∞} :
n < height p ↔ ∃ c : StrictSeries α, c.top = p ∧ c.length = n + 1 := by
  cases' n using ENat.recTopCoe with n
  . simp
  . erw [←(ENat.add_one_le_iff <| ENat.coe_ne_top _), le_height_iff]
    -- show (n + 1 : ℕ) ≤ (_ : ℕ∞) ↔ _
    -- norm_cast
    -- rw [le_height_iff]
    norm_cast