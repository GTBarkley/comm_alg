import Mathlib.Order.KrullDimension
import Mathlib.Order.JordanHolder
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Order.Height
import CommAlg.krull


#check (p q : PrimeSpectrum _) → (p ≤ q)
#check Preorder (PrimeSpectrum _)

-- Dimension of a ring
#check krullDim (PrimeSpectrum _)

-- Length of a module
#check krullDim (Submodule _ _)

#check JordanHolderLattice


section Chains

variable {α : Type _} [Preorder α] (s : Set α)

def finFun_to_list {n : ℕ} : (Fin n → α) → List α := by sorry

def series_to_chain : StrictSeries s → s.subchain
| ⟨length, toFun, strictMono⟩ => 
    ⟨ finFun_to_list (fun x => toFun x),
      sorry⟩

-- there should be a coercion from WithTop ℕ to WithBot (WithTop ℕ) but it doesn't seem to work
-- it looks like this might be because someone changed the instance from CoeCT to Coe during the port
-- actually it looks like we can coerce to WithBot (ℕ∞) fine
lemma twoHeights : s ≠ ∅ → (some (Set.chainHeight s) : WithBot (WithTop ℕ)) = krullDim s := by
  intro hs
  unfold Set.chainHeight
  unfold krullDim
  have hKrullSome : ∃n, krullDim s = some n := by
    
    sorry
  -- norm_cast
  sorry

end Chains

section Krull

variable (R : Type _) [CommRing R] (M : Type _) [AddCommGroup M] [Module R M]

open Ideal

-- chain of primes 
#check height 

lemma lt_height_iff {𝔭 : PrimeSpectrum R} {n : ℕ∞} :
  height 𝔭 > n ↔ ∃ c : List (PrimeSpectrum R), c ∈ {I : PrimeSpectrum R | I < 𝔭}.subchain ∧ c.length = n + 1 := sorry

lemma lt_height_iff' {𝔭 : PrimeSpectrum R} {n : ℕ∞} : 
height 𝔭 > n ↔ ∃ c : List (PrimeSpectrum R), c.Chain' (· < ·) ∧ (∀ 𝔮 ∈ c, 𝔮 < 𝔭) ∧ c.length = n + 1 := by
  rcases n with _ | n
  . constructor <;> intro h <;> exfalso
    . exact (not_le.mpr h) le_top
    . -- change ∃c, _ ∧ _ ∧ ((List.length c : ℕ∞) = ⊤ + 1) at h
      -- rw [WithTop.top_add] at h
      tauto
  have (m : ℕ∞) : m > some n ↔ m ≥ some (n + 1) := by
    symm
    show (n + 1 ≤ m ↔ _ )
    apply ENat.add_one_le_iff
    exact ENat.coe_ne_top _
  rw [this]
  unfold Ideal.height
  show ((↑(n + 1):ℕ∞) ≤ _) ↔ ∃c, _ ∧ _ ∧ ((_ : WithTop ℕ) = (_:ℕ∞))
  rw [{J | J < 𝔭}.le_chainHeight_iff]
  show (∃ c, (List.Chain' _ c ∧ ∀𝔮, 𝔮 ∈ c → 𝔮 < 𝔭) ∧ _) ↔ _
  -- have h := fun (c : List (PrimeSpectrum R)) => (@WithTop.coe_eq_coe _ (List.length c) n) 
  constructor <;> rintro ⟨c, hc⟩ <;> use c --<;> tauto--<;> exact ⟨hc.1, by tauto⟩
  . --rw [and_assoc]
    -- show _ ∧ _ ∧ _
    --exact ⟨hc.1, _⟩
    tauto
  . change _ ∧ _ ∧ (List.length c : ℕ∞) = n + 1 at hc
    norm_cast at hc
    tauto

lemma lt_height_iff'' {𝔭 : PrimeSpectrum R} {n : ℕ∞} : 
height 𝔭 > (n : WithBot ℕ∞) ↔ ∃ c : List (PrimeSpectrum R), c.Chain' (· < ·) ∧ (∀ 𝔮 ∈ c, 𝔮 < 𝔭) ∧ c.length = n + 1 := by
  show (_ < _) ↔ _
  rw [WithBot.coe_lt_coe]
  exact lt_height_iff' _

lemma height_le_iff {𝔭 : PrimeSpectrum R} {n : ℕ∞} : 
  height 𝔭 ≤ n ↔ ∀ c : List (PrimeSpectrum R), c ∈ {I : PrimeSpectrum R | I < 𝔭}.subchain ∧ c.length = n + 1 := by
  sorry

lemma krullDim_nonneg_of_nontrivial [Nontrivial R] : ∃ n : ℕ∞, Ideal.krullDim R = n := by
  have h := dim_eq_bot_iff.not.mpr (not_subsingleton R)
  lift (Ideal.krullDim R) to ℕ∞ using h with k
  use k

-- lemma krullDim_le_iff' (R : Type _) [CommRing R] {n : WithBot ℕ∞} : 
--   Ideal.krullDim R ≤ n ↔ (∀ c : List (PrimeSpectrum R), c.Chain' (· < ·) → c.length ≤ n + 1) := by
--     sorry

-- lemma krullDim_ge_iff' (R : Type _) [CommRing R] {n : WithBot ℕ∞} : 
--   Ideal.krullDim R ≥ n ↔ ∃ c : List (PrimeSpectrum R), c.Chain' (· < ·) ∧ c.length = n + 1 := sorry

lemma primeSpectrum_empty_of_subsingleton (x : PrimeSpectrum R) [Subsingleton R] : False :=
  x.1.ne_top_iff_one.1 x.2.1 <| Eq.substr (Subsingleton.elim 1 (0 : R)) x.1.zero_mem

lemma primeSpectrum_empty_iff : IsEmpty (PrimeSpectrum R) ↔ Subsingleton R := by
  constructor
  . contrapose
    rw [not_isEmpty_iff, ←not_nontrivial_iff_subsingleton, not_not]
    apply PrimeSpectrum.instNonemptyPrimeSpectrum
  . intro h
    by_contra hneg
    rw [not_isEmpty_iff] at hneg
    rcases hneg with ⟨a, ha⟩
    exact primeSpectrum_empty_of_subsingleton R ⟨a, ha⟩

/-- A ring has Krull dimension -∞ if and only if it is the zero ring -/
lemma dim_eq_bot_iff : krullDim R = ⊥ ↔ Subsingleton R := by
  unfold Ideal.krullDim
  rw [←primeSpectrum_empty_iff, iSup_eq_bot]
  constructor <;> intro h
  . rw [←not_nonempty_iff]
    rintro ⟨a, ha⟩
    specialize h ⟨a, ha⟩
    tauto
  . rw [h.forall_iff]
    trivial

#check (sorry : False)
#check (sorryAx)
#check (4 : WithBot ℕ∞)
#check List.sum
#check (_ ∈ (_ : List _))
variable (α : Type ) 
#synth Membership α (List α)
#check bot_lt_iff_ne_bot
-- #check ((4 : ℕ∞) : WithBot (WithTop ℕ))
-- #check ( (Set.chainHeight s) : WithBot (ℕ∞))

/-- The converse of this is false, because the definition of "dimension ≤ 1" in mathlib
  applies only to dimension zero rings and domains of dimension 1. -/
lemma dim_le_one_of_dimLEOne :  Ring.DimensionLEOne R → krullDim R ≤ (1 : ℕ) := by
  rw [krullDim_le_iff R 1]
  -- unfold Ring.DimensionLEOne
  intro H p
  -- have Hp := H p.asIdeal
  -- have Hp := fun h => (Hp h) p.IsPrime
  apply le_of_not_gt
  intro h
  rcases ((lt_height_iff'' R).mp h) with ⟨c, ⟨hc1, hc2, hc3⟩⟩
  norm_cast at hc3
  rw [List.chain'_iff_get] at hc1
  specialize hc1 0 (by rw [hc3]; simp)
  -- generalize hq0 : List.get _ _ = q0 at hc1
  set q0 : PrimeSpectrum R := List.get c { val := 0, isLt := _ }
  set q1 : PrimeSpectrum R := List.get c { val := 1, isLt := _ } 
  -- have hq0 : q0 ∈ c := List.get_mem _ _ _ 
  -- have hq1 : q1 ∈ c := List.get_mem _ _ _
  specialize hc2 q1 (List.get_mem _ _ _)
  -- have aa := (bot_le : (⊥ : Ideal R) ≤ q0.asIdeal)
  change q0.asIdeal < q1.asIdeal at hc1
  have q1nbot := Trans.trans (bot_le : ⊥ ≤ q0.asIdeal) hc1
  specialize H q1.asIdeal (bot_lt_iff_ne_bot.mp q1nbot) q1.IsPrime
  -- change q1.asIdeal < p.asIdeal at hc2
  apply IsPrime.ne_top p.IsPrime
  apply (IsCoatom.lt_iff H.out).mp
  exact hc2
  --refine Iff.mp radical_eq_top (?_ (id (Eq.symm hc3))) 

lemma not_maximal_of_lt_prime {p : Ideal R} {q : Ideal R} (hq : IsPrime q) (h : p < q) : ¬IsMaximal p := by
  intro hp
  apply IsPrime.ne_top hq
  apply (IsCoatom.lt_iff hp.out).mp
  exact h

lemma dim_le_zero_iff : krullDim R ≤ 0 ↔ ∀ I : PrimeSpectrum R, IsMaximal I.asIdeal := by
  show ((_ : WithBot ℕ∞) ≤ (0 : ℕ)) ↔ _
  rw [krullDim_le_iff R 0]
  constructor <;> intro h I
  . contrapose! h
    have ⟨𝔪, h𝔪⟩ := I.asIdeal.exists_le_maximal (IsPrime.ne_top I.IsPrime)
    let 𝔪p := (⟨𝔪, IsMaximal.isPrime h𝔪.1⟩ : PrimeSpectrum R)
    have hstrct : I < 𝔪p := by
      apply lt_of_le_of_ne h𝔪.2
      intro hcontr
      rw [hcontr] at h
      exact h h𝔪.1
    use 𝔪p
    show (_ : WithBot ℕ∞) > (0 : ℕ∞)
    rw [_root_.lt_height_iff'']
    use [I]
    constructor
    . exact List.chain'_singleton _
    . constructor
      . intro I' hI'
        simp at hI'
        rwa [hI']
      . simp
  . contrapose! h
    change (_ : WithBot ℕ∞) > (0 : ℕ∞) at h
    rw [_root_.lt_height_iff''] at h
    obtain ⟨c, _, hc2, hc3⟩ := h
    norm_cast at hc3
    rw [List.length_eq_one] at hc3
    obtain ⟨𝔮, h𝔮⟩ := hc3
    use 𝔮
    specialize hc2 𝔮 (h𝔮 ▸ (List.mem_singleton.mpr rfl))
    apply not_maximal_of_lt_prime _ I.IsPrime
    exact hc2

end Krull

section iSupWithBot

variable {α : Type _} [CompleteSemilatticeSup α] {I : Type _} (f : I → α)

#synth SupSet (WithBot ℕ∞)

protected lemma WithBot.iSup_ge_coe_iff {a : α} : 
  (a ≤ ⨆ i : I, (f i : WithBot α) ) ↔ ∃ i : I, f i ≥ a := by
  rw [WithBot.coe_le_iff]
  sorry

end iSupWithBot

section myGreatElab
open Lean Meta Elab

syntax (name := lhsStx) "lhs% " term:max : term
syntax (name := rhsStx) "rhs% " term:max : term

@[term_elab lhsStx, term_elab rhsStx]
def elabLhsStx : Term.TermElab := fun stx expectedType? =>
  match stx with
  | `(lhs% $t) => do
    let (lhs, _, eq) ← mkExpected expectedType?
    discard <| Term.elabTermEnsuringType t eq
    return lhs
  | `(rhs% $t) => do
    let (_, rhs, eq) ← mkExpected expectedType?
    discard <| Term.elabTermEnsuringType t eq
    return rhs
  | _ => throwUnsupportedSyntax
where
  mkExpected expectedType? := do
    let α ←
      if let some expectedType := expectedType? then
        pure expectedType
      else
        mkFreshTypeMVar
    let lhs ← mkFreshExprMVar α
    let rhs ← mkFreshExprMVar α
    let u ← getLevel α
    let eq := mkAppN (.const ``Eq [u]) #[α, lhs, rhs]
    return (lhs, rhs, eq)

#check lhs% (add_comm 1 2)
#check rhs% (add_comm 1 2)
#check lhs% (add_comm _ _ : _ = 1 + 2)

example (x y : α) (h : x = y) : lhs% h = rhs% h := h

def lhsOf {α : Sort _} {x y : α} (h : x = y) : α := x

#check lhsOf (add_comm 1 2)