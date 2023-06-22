/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the Mathlib file LICENSE.
Authors: Chris Hughes, Grant Barkley
-/
import Mathlib.Order.Lattice
import Mathlib.Data.List.Sort
import Mathlib.Logic.Equiv.Fin
import Mathlib.Logic.Equiv.Functor
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Monotone.Basic

structure StrictSeries (X : Type u) [LT X] : Type u where
  length : ℕ
  toFun : Fin (length + 1) → X
  step' : ∀ i : Fin length, (toFun (Fin.castSucc i)) < (toFun (Fin.succ i))
  --StrictMono toFun

section List

-- TODO: move this to Mathlib.Data.List.Basic
@[simp]
theorem List.getLast_tail {X : Type _} {l : List X} {h : l.tail ≠ []} :
l.tail.getLast h = l.getLast (fun c => (c ▸ h) List.tail_nil) := by
  cases l
  . simp
  . rw [List.getLast_cons]; simp; assumption

end List

namespace StrictSeries

section FinLemmas

-- TODO: move these to `VecNotation` and rename them to better describe their statement
variable {α : Type _} {m n : ℕ} (a : Fin m.succ → α) (b : Fin n.succ → α)

theorem append_castAdd_aux (i : Fin m) :
    Matrix.vecAppend (Nat.add_succ _ _).symm (a ∘ Fin.castSucc) b
      (Fin.castSucc <| Fin.castAdd n i) =
      a (Fin.castSucc i) := by
  cases i
  simp [Matrix.vecAppend_eq_ite, *]
#align composition_series.append_cast_add_aux StrictSeries.append_castAdd_aux

theorem append_succ_castAdd_aux (i : Fin m) (h : a (Fin.last _) = b 0) :
    Matrix.vecAppend (Nat.add_succ _ _).symm (a ∘ Fin.castSucc) b (Fin.castAdd n i).succ =
      a i.succ := by
  cases' i with i hi
  simp only [Matrix.vecAppend_eq_ite, hi, Fin.succ_mk, Function.comp_apply, Fin.castSucc_mk,
    Fin.val_mk, Fin.castAdd_mk]
  split_ifs with h_1
  · rfl
  · have : i + 1 = m := le_antisymm hi (le_of_not_gt h_1)
    calc
      b ⟨i + 1 - m, by simp [this]⟩ = b 0 := congr_arg b (by simp [Fin.ext_iff, this])
      _ = a (Fin.last _) := h.symm
      _ = _ := congr_arg a (by simp [Fin.ext_iff, this])
#align composition_series.append_succ_cast_add_aux StrictSeries.append_succ_castAdd_aux

theorem append_natAdd_aux (i : Fin n) :
    Matrix.vecAppend (Nat.add_succ _ _).symm (a ∘ Fin.castSucc) b
      (Fin.castSucc <| Fin.natAdd m i) =
      b (Fin.castSucc i) := by
  cases i
  simp only [Matrix.vecAppend_eq_ite, Nat.not_lt_zero, Fin.natAdd_mk, add_lt_iff_neg_left,
    add_tsub_cancel_left, dif_neg, Fin.castSucc_mk, not_false_iff, Fin.val_mk]
#align composition_series.append_nat_add_aux StrictSeries.append_natAdd_aux

theorem append_succ_natAdd_aux (i : Fin n) :
    Matrix.vecAppend (Nat.add_succ _ _).symm (a ∘ Fin.castSucc) b (Fin.natAdd m i).succ =
      b i.succ := by
  cases' i with i hi
  simp only [Matrix.vecAppend_eq_ite, add_assoc, Nat.not_lt_zero, Fin.natAdd_mk,
    add_lt_iff_neg_left, add_tsub_cancel_left, Fin.succ_mk, dif_neg, not_false_iff, Fin.val_mk]
#align composition_series.append_succ_nat_add_aux StrictSeries.append_succ_natAdd_aux

end FinLemmas


section LT

variable {X : Type u} [LT X]

instance IsEmpty [IsEmpty X] : IsEmpty (StrictSeries X) :=
  ⟨fun s => IsEmpty.false <| s.toFun 0⟩

instance coeFun : CoeFun (StrictSeries X) fun x => Fin (x.length + 1) → X where
  coe := StrictSeries.toFun

instance inhabited [Inhabited X] : Inhabited (StrictSeries X) :=
  ⟨{  length := 0
      toFun := default
      step' := fun x => x.elim0 }⟩

instance Nonempty [Nonempty X] : Nonempty (StrictSeries X) :=
  ⟨{  length := 0
      toFun := Nonempty.some inferInstance
      step' := fun x => x.elim0 }⟩

theorem step (s : StrictSeries X) :
    ∀ i : Fin s.length, (s (Fin.castSucc i)) < (s (Fin.succ i)) :=
  s.step'

theorem coeFn_mk (length : ℕ) (toFun step) :
    (@StrictSeries.mk X _ length toFun step : Fin length.succ → X) = toFun :=
  rfl

theorem lt_succ (s : StrictSeries X) (i : Fin s.length) :
    s (Fin.castSucc i) < s (Fin.succ i) :=
   (s.step _)

instance membership : Membership X (StrictSeries X) :=
  ⟨fun x s => x ∈ Set.range s⟩

theorem mem_def {x : X} {s : StrictSeries X} : x ∈ s ↔ x ∈ Set.range s :=
  Iff.rfl

/-- The ordered `List X` of elements of a `StrictSeries X`. -/
def toList (s : StrictSeries X) : List X :=
  List.ofFn s

/-- Two `StrictSeries` are equal if they are the same length and
have the same `i`th element for every `i` -/
theorem ext_fun {s₁ s₂ : StrictSeries X} (hl : s₁.length = s₂.length)
    (h : ∀ i, s₁ i = s₂ (Fin.cast (congr_arg Nat.succ hl) i)) : s₁ = s₂ := by
  cases s₁; cases s₂
  -- Porting note: `dsimp at *` doesn't work. Why?
  dsimp at hl h
  subst hl
  simpa [Function.funext_iff] using h

@[simp]
theorem length_toList (s : StrictSeries X) : s.toList.length = s.length + 1 := by
  rw [toList, List.length_ofFn]

theorem toList_ne_nil (s : StrictSeries X) : s.toList ≠ [] := by
  rw [← List.length_pos_iff_ne_nil, length_toList]; exact Nat.succ_pos _

theorem chain'_toList (s : StrictSeries X) : List.Chain' (· < ·) s.toList :=
  List.chain'_iff_get.2
    (by
      intro i hi
      simp only [toList, List.get_ofFn]
      rw [length_toList] at hi
      exact s.step ⟨i, hi⟩)

@[simp]
theorem mem_toList {s : StrictSeries X} {x : X} : x ∈ s.toList ↔ x ∈ s := by
  rw [toList, List.mem_ofFn, mem_def]

/-- Make a `StrictSeries X` from the ordered list of its elements. -/
def ofList (l : List X) (hl : l ≠ []) (hc : List.Chain' (· < ·) l) : StrictSeries X
    where
  length := l.length - 1
  toFun i :=
    l.nthLe i
      (by
        conv_rhs => rw [← tsub_add_cancel_of_le (Nat.succ_le_of_lt (List.length_pos_of_ne_nil hl))]
        exact i.2)
  step' := fun ⟨i, hi⟩ => List.chain'_iff_get.1 hc i hi

theorem length_ofList (l : List X) (hl : l ≠ []) (hc : List.Chain' (· < ·) l) :
    (ofList l hl hc).length = l.length - 1 :=
  rfl

theorem ofList_toList (s : StrictSeries X) :
    ofList s.toList s.toList_ne_nil s.chain'_toList = s := by
  refine' ext_fun _ _
  · rw [length_ofList, length_toList, Nat.succ_sub_one]
  · rintro ⟨i, hi⟩
    simp [ofList, toList, -List.ofFn_succ]

@[simp]
theorem ofList_toList' (s : StrictSeries X) :
    ofList s.toList s.toList_ne_nil s.chain'_toList = s :=
  ofList_toList s

@[simp]
theorem toList_ofList (l : List X) (hl : l ≠ []) (hc : List.Chain' (· < ·) l) :
    toList (ofList l hl hc) = l := by
  refine' List.ext_get _ _
  · rw [length_toList, length_ofList,
      tsub_add_cancel_of_le (Nat.succ_le_of_lt <| List.length_pos_of_ne_nil hl)]
  · intro i hi hi'
    dsimp [ofList, toList]
    rw [List.get_ofFn]
    rfl

theorem toList_injective : Function.Injective (@StrictSeries.toList X _) :=
  fun s₁ s₂ (h : List.ofFn s₁ = List.ofFn s₂) => by
  have h₁ : s₁.length = s₂.length :=
    Nat.succ_injective
      ((List.length_ofFn s₁).symm.trans <| (congr_arg List.length h).trans <| List.length_ofFn s₂)
  have h₂ : ∀ i : Fin s₁.length.succ, s₁ i = s₂ (Fin.cast (congr_arg Nat.succ h₁) i) :=
    congr_fun <| List.ofFn_injective <| h.trans <| List.ofFn_congr (congr_arg Nat.succ h₁).symm _
  cases s₁
  cases s₂
  dsimp at h h₁ h₂
  subst h₁
  simp only [mk.injEq, heq_eq_eq, true_and]
  simp only [Fin.cast_refl] at h₂
  exact funext h₂

theorem ext_list {s₁ s₂ : StrictSeries X} (h : toList s₁ = toList s₂) : s₁ = s₂ := 
  toList_injective h

def ofElement (x : X) : StrictSeries X where
  length := 0
  toFun _ := x
  step' := by simp

@[simp]
theorem length_ofElement (x : X) :
    (ofElement x).length = 0 := rfl

@[simp]
theorem toList_ofElement (x : X) : toList (ofElement x) = [x] := by 
    obtain ⟨a, ha⟩ := List.length_eq_one.mp (length_ofElement x ▸ length_toList <| ofElement x)
    have := List.eq_of_mem_singleton <| ha ▸ (mem_toList.mpr ⟨0, rfl⟩ : x ∈ toList (ofElement x))
    rw [(ha : toList (ofElement x) = _), this]

@[simp]
theorem mem_ofElement (x : X) {y : X} : y ∈ (ofElement x) ↔ y = x := by
  rw [←mem_toList, toList_ofElement, List.mem_singleton]

@[simp]
theorem ofList_singleton {x : X} {hne} {hch} : ofList [x] hne hch = ofElement x := by
  apply ext_list
  rw [toList_ofList, toList_ofElement]

theorem length_eq_zero {s : StrictSeries X} :
  s.length = 0 ↔ ∃ x, s = ofElement x := 
  ⟨fun h =>  
    have ⟨a, ha⟩ := List.length_eq_one.mp (h ▸ (length_toList s))
    ⟨a, by apply ext_list; rw [ha, toList_ofElement]⟩, 
  fun ⟨x, h⟩ => h.symm ▸ length_ofElement x⟩

theorem ofElement_of_length_zero {s : StrictSeries X} (h : s.length = 0) (hx : x ∈ s) :
  s = ofElement x := by
  have ⟨y, hy⟩ := length_eq_zero.mp h
  -- bug? can't inline this
  have := mem_ofElement y |>.mp <| hy ▸ hx
  rwa [this]

/-- The last element of a `StrictSeries` -/
def top (s : StrictSeries X) : X :=
  s (Fin.last _)

theorem top_mem (s : StrictSeries X) : s.top ∈ s :=
  mem_def.2 (Set.mem_range.2 ⟨Fin.last _, rfl⟩)

@[simp]
theorem ofElement_top {x : X} : (ofElement x).top = x := rfl

@[simp]
theorem getLast_toList_eq_top (s : StrictSeries X) : s.toList.getLast s.toList_ne_nil = s.top := by
  erw [List.last_ofFn]; rfl

@[simp]
theorem top_ofList {l : List X} {hnn} {hcn} : (ofList l hnn hcn).top = l.getLast hnn := by
  rw [←getLast_toList_eq_top]; simp

theorem length_eq_zero_top {s : StrictSeries X} : s.length = 0 ↔ s = ofElement s.top :=
  ⟨fun h => ofElement_of_length_zero h (top_mem s), fun h => h.symm ▸ length_ofElement _⟩

/-- The first element of a `StrictSeries` -/
def bot (s : StrictSeries X) : X :=
  s 0

theorem bot_mem (s : StrictSeries X) : s.bot ∈ s :=
  mem_def.2 (Set.mem_range.2 ⟨0, rfl⟩)

@[simp]
theorem ofElement_bot {x : X} : (ofElement x).bot = x := rfl

theorem length_eq_zero_bot {s : StrictSeries X} : s.length = 0 ↔ s = ofElement s.bot :=
  ⟨fun h => ofElement_of_length_zero h (bot_mem s), fun h => h.symm ▸ length_ofElement _⟩

/-- Remove the largest element from a `StrictSeries`. If the toFun `s`
has length zero, then `s.eraseTop = s` -/
@[simps]
def eraseTop (s : StrictSeries X) : StrictSeries X
    where
  length := s.length - 1
  toFun i := s ⟨i, lt_of_lt_of_le i.2 (Nat.succ_le_succ tsub_le_self)⟩
  step' i := by
    have := s.step ⟨i, lt_of_lt_of_le i.2 tsub_le_self⟩
    cases i
    exact this

theorem top_eraseTop (s : StrictSeries X) :
    s.eraseTop.top = s ⟨s.length - 1, lt_of_le_of_lt tsub_le_self (Nat.lt_succ_self _)⟩ :=
  show s _ = s _ from
    congr_arg s
      (by
        ext
        simp only [eraseTop_length, Fin.val_last, Fin.coe_castSucc, Fin.coe_ofNat_eq_mod,
          Fin.val_mk])

@[simp]
theorem bot_eraseTop (s : StrictSeries X) : s.eraseTop.bot = s.bot :=
  rfl

def eraseBot (s : StrictSeries X) : StrictSeries X :=
  if h : s.length = 0 then s
  else
    ofList (s.toList.tail) 
    (fun hc => h <| s.length_toList ▸ hc ▸ s.toList.length_tail |>.symm) s.chain'_toList.tail

#check Function.invFun

theorem top_eraseBot (s : StrictSeries X) : s.eraseBot.top = s.top :=
  if h : s.length = 0 then by rw [eraseBot, dif_pos h]
  else by rw [eraseBot, dif_neg h]; simp

/-- Append two composition toFun `s₁` and `s₂` such that
the least element of `s₁` is the maximum element of `s₂`. -/
@[simps length]
def append (s₁ s₂ : StrictSeries X) (h : s₁.top = s₂.bot) : StrictSeries X where
  length := s₁.length + s₂.length
  toFun := Matrix.vecAppend (Nat.add_succ s₁.length s₂.length).symm (s₁ ∘ Fin.castSucc) s₂
  step' i := by
    refine' Fin.addCases _ _ i
    · intro i
      rw [append_succ_castAdd_aux _ _ _ h, append_castAdd_aux]
      exact s₁.step i
    · intro i
      rw [append_natAdd_aux, append_succ_natAdd_aux]
      exact s₂.step i

theorem coe_append (s₁ s₂ : StrictSeries X) (h) :
    ⇑(s₁.append s₂ h) = Matrix.vecAppend (Nat.add_succ _ _).symm (s₁ ∘ Fin.castSucc) s₂ :=
  rfl

@[simp]
theorem append_castAdd {s₁ s₂ : StrictSeries X} (h : s₁.top = s₂.bot) (i : Fin s₁.length) :
    append s₁ s₂ h (Fin.castSucc <| Fin.castAdd s₂.length i) = s₁ (Fin.castSucc i) := by
  rw [coe_append, append_castAdd_aux _ _ i]

@[simp]
theorem append_succ_castAdd {s₁ s₂ : StrictSeries X} (h : s₁.top = s₂.bot)
    (i : Fin s₁.length) : append s₁ s₂ h (Fin.castAdd s₂.length i).succ = s₁ i.succ := by
  rw [coe_append, append_succ_castAdd_aux _ _ _ h]

@[simp]
theorem append_natAdd {s₁ s₂ : StrictSeries X} (h : s₁.top = s₂.bot) (i : Fin s₂.length) :
    append s₁ s₂ h (Fin.castSucc <| Fin.natAdd s₁.length i) = s₂ (Fin.castSucc i) := by
  rw [coe_append, append_natAdd_aux _ _ i]

@[simp]
theorem append_succ_natAdd {s₁ s₂ : StrictSeries X} (h : s₁.top = s₂.bot) (i : Fin s₂.length) :
    append s₁ s₂ h (Fin.natAdd s₁.length i).succ = s₂ i.succ := by
  rw [coe_append, append_succ_natAdd_aux _ _ i]

/-- Add an element to the top of a `StrictSeries` -/
@[simps length]
def snoc (s : StrictSeries X) (x : X) (hsat : s.top < x) : StrictSeries X where
  length := s.length + 1
  toFun := Fin.snoc s x
  step' i := by
    refine' Fin.lastCases _ _ i
    · rwa [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, ← top]
    · intro i
      rw [Fin.snoc_castSucc, ← Fin.castSucc_fin_succ, Fin.snoc_castSucc]
      exact s.step _
#align composition_series.snoc StrictSeries.snoc

@[simp]
theorem top_snoc (s : StrictSeries X) (x : X) (hsat : s.top < x) :
    (snoc s x hsat).top = x :=
  Fin.snoc_last (α := fun _ => X) _ _
#align composition_series.top_snoc StrictSeries.top_snoc

@[simp]
theorem snoc_last (s : StrictSeries X) (x : X) (hsat : s.top < x) :
    snoc s x hsat (Fin.last (s.length + 1)) = x :=
  Fin.snoc_last (α := fun _ => X) _ _
#align composition_series.snoc_last StrictSeries.snoc_last

@[simp]
theorem snoc_castSucc (s : StrictSeries X) (x : X) (hsat : s.top < x)
    (i : Fin (s.length + 1)) : snoc s x hsat (Fin.castSucc i) = s i :=
  Fin.snoc_castSucc (α := fun _ => X) _ _ _
#align composition_series.snoc_cast_succ StrictSeries.snoc_castSucc

@[simp]
theorem bot_snoc (s : StrictSeries X) (x : X) (hsat : s.top < x) :
    (snoc s x hsat).bot = s.bot := by rw [bot, bot, ← snoc_castSucc s _ _ 0, Fin.castSucc_zero]
#align composition_series.bot_snoc StrictSeries.bot_snoc

theorem mem_snoc {s : StrictSeries X} {x y : X} {hsat : s.top < x} :
    y ∈ snoc s x hsat ↔ y ∈ s ∨ y = x := by
  simp only [snoc, mem_def]
  constructor
  · rintro ⟨i, rfl⟩
    refine' Fin.lastCases _ (fun i => _) i
    · right
      simp
    · left
      simp
  · intro h
    rcases h with (⟨i, rfl⟩ | rfl)
    · use Fin.castSucc i
      simp
    · use Fin.last _
      simp
#align composition_series.mem_snoc StrictSeries.mem_snoc


end LT

section Preorder

variable {X : Type _} [Preorder X]

protected theorem strictMono (s : StrictSeries X) : StrictMono s :=
  Fin.strictMono_iff_lt_succ.2 s.lt_succ

protected theorem injective (s : StrictSeries X) : Function.Injective s :=
  s.strictMono.injective

@[simp]
protected theorem inj (s : StrictSeries X) {i j : Fin s.length.succ} : s i = s j ↔ i = j :=
  s.injective.eq_iff

theorem total {s : StrictSeries X} {x y : X} (hx : x ∈ s) (hy : y ∈ s) : x ≤ y ∨ y ≤ x := by
  rcases Set.mem_range.1 hx with ⟨i, rfl⟩
  rcases Set.mem_range.1 hy with ⟨j, rfl⟩
  rw [s.strictMono.le_iff_le, s.strictMono.le_iff_le]
  exact le_total i j

theorem toList_sorted (s : StrictSeries X) : s.toList.Sorted (· < ·) :=
  List.pairwise_iff_get.2 fun i j h => by
    dsimp [toList]
    rw [List.get_ofFn, List.get_ofFn]
    exact s.strictMono h

theorem toList_nodup (s : StrictSeries X) : s.toList.Nodup :=
  s.toList_sorted.nodup

/-- Two `StrictSeries` on a preorder are equal if they have the same elements. 
See also `ext_fun` and `ext_list`. -/
@[ext]
theorem ext {s₁ s₂ : StrictSeries X} (h : ∀ x, x ∈ s₁ ↔ x ∈ s₂) : s₁ = s₂ :=
  toList_injective <|
    List.eq_of_perm_of_sorted
      (by
        classical
        exact List.perm_of_nodup_nodup_toFinset_eq s₁.toList_nodup s₂.toList_nodup
          (Finset.ext <| by simp [*]))
      s₁.toList_sorted s₂.toList_sorted

@[simp]
theorem le_top {s : StrictSeries X} (i : Fin (s.length + 1)) : s i ≤ s.top :=
  s.strictMono.monotone (Fin.le_last _)

theorem le_top_of_mem {s : StrictSeries X} {x : X} (hx : x ∈ s) : x ≤ s.top :=
  let ⟨_i, hi⟩ := Set.mem_range.2 hx
  hi ▸ le_top _

@[simp]
theorem bot_le {s : StrictSeries X} (i : Fin (s.length + 1)) : s.bot ≤ s i :=
  s.strictMono.monotone (Fin.zero_le _)

theorem bot_le_of_mem {s : StrictSeries X} {x : X} (hx : x ∈ s) : s.bot ≤ x :=
  let ⟨_i, hi⟩ := Set.mem_range.2 hx
  hi ▸ bot_le _

-- TODO this should be in section LT
theorem length_pos_of_mem_ne {s : StrictSeries X} {x y : X} (hx : x ∈ s) (hy : y ∈ s)
    (hxy : x ≠ y) : 0 < s.length :=
  let ⟨i, hi⟩ := hx
  let ⟨j, hj⟩ := hy
  have hij : i ≠ j := mt s.inj.2 fun h => hxy (hi ▸ hj ▸ h)
  hij.lt_or_lt.elim
    (fun hij => lt_of_le_of_lt (zero_le (i : ℕ)) (lt_of_lt_of_le hij (Nat.le_of_lt_succ j.2)))
      fun hji => lt_of_le_of_lt (zero_le (j : ℕ)) (lt_of_lt_of_le hji (Nat.le_of_lt_succ i.2))

-- TODO this should be in section LT
theorem forall_mem_eq_of_length_eq_zero {s : StrictSeries X} (hs : s.length = 0) {x y}
    (hx : x ∈ s) (hy : y ∈ s) : x = y :=
  by_contradiction fun hxy => pos_iff_ne_zero.1 (length_pos_of_mem_ne hx hy hxy) hs

theorem eraseTop_top_le (s : StrictSeries X) : s.eraseTop.top ≤ s.top := by
  simp [eraseTop, top, s.strictMono.le_iff_le, Fin.le_iff_val_le_val, tsub_le_self]

-- TODO this should be in section LT
theorem mem_eraseTop_of_ne_of_mem {s : StrictSeries X} {x : X} (hx : x ≠ s.top) (hxs : x ∈ s) :
    x ∈ s.eraseTop := by
  rcases hxs with ⟨i, rfl⟩
  have hi : (i : ℕ) < (s.length - 1).succ := by
    conv_rhs => rw [← Nat.succ_sub (length_pos_of_mem_ne ⟨i, rfl⟩ s.top_mem hx), Nat.succ_sub_one]
    exact lt_of_le_of_ne (Nat.le_of_lt_succ i.2) (by simpa [top, s.inj, Fin.ext_iff] using hx)
  refine' ⟨Fin.castSucc i, _⟩
  simp [Fin.ext_iff, Nat.mod_eq_of_lt hi]

theorem mem_eraseTop {s : StrictSeries X} {x : X} (h : 0 < s.length) :
    x ∈ s.eraseTop ↔ x ≠ s.top ∧ x ∈ s := by
  simp only [mem_def]
  dsimp only [eraseTop]
  constructor
  · rintro ⟨i, rfl⟩
    have hi : (i : ℕ) < s.length := by
      conv_rhs => rw [← Nat.succ_sub_one s.length, Nat.succ_sub h]
      exact i.2
    simp [top, Fin.ext_iff, ne_of_lt hi, -Set.mem_range, Set.mem_range_self]
  · intro h
    exact mem_eraseTop_of_ne_of_mem h.1 h.2

theorem lt_top_of_mem_eraseTop {s : StrictSeries X} {x : X} (h : 0 < s.length)
    (hx : x ∈ s.eraseTop) : x < s.top := by
    rw [mem_eraseTop h] at hx
    let ⟨i, hi⟩ := Set.mem_range.2 hx.2
    rw [←hi]
    apply s.strictMono
    apply lt_of_le_of_ne i.le_last
    intro hc
    exact ((hc ▸ hi).symm ▸ hx).1 rfl
    --hi ▸ le_top _
  -- lt_of_le_of_ne (le_top_of_mem ((mem_eraseTop h).1 hx).2) ((mem_eraseTop h).1 hx).1
-- #align composition_series.lt_top_of_mem_erase_top StrictSeries.lt_top_of_mem_eraseTop

theorem isMaximal_eraseTop_top {s : StrictSeries X} (h : 0 < s.length) :
    s.eraseTop.top < s.top := lt_top_of_mem_eraseTop h (top_mem _)
--   have : s.length - 1 + 1 = s.length := by
--     conv_rhs => rw [← Nat.succ_sub_one s.length]; rw [Nat.succ_sub h]
--   rw [top_eraseTop, top]
--   convert s.step ⟨s.length - 1, Nat.sub_lt h zero_lt_one⟩; ext; simp [this]
-- #align composition_series.is_maximal_erase_top_top StrictSeries.isMaximal_eraseTop_top

-- TODO should be in LT
theorem eq_snoc_eraseTop {s : StrictSeries X} (h : 0 < s.length) :
    s = snoc (eraseTop s) s.top (isMaximal_eraseTop_top h) := by
  ext x
  simp [mem_snoc, mem_eraseTop h]
  by_cases h : x = s.top <;> simp [*, s.top_mem]

-- TODO should be in LT
@[simp]
theorem snoc_eraseTop_top {s : StrictSeries X} (h : s.eraseTop.top < s.top) :
    s.eraseTop.snoc s.top h = s :=
  have h : 0 < s.length :=
    Nat.pos_of_ne_zero
      (by
        intro hs
        refine' ne_of_gt h _
        simp [top, Fin.ext_iff, hs])
  (eq_snoc_eraseTop h).symm

-- section `Equivalent` doesn't apply here

theorem length_eq_zero_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero {s₁ s₂ : StrictSeries X}
    (hb : s₁.bot = s₂.bot) (ht : s₁.top = s₂.top) (hs₁ : s₁.length = 0) : s₂.length = 0 := by
  have : s₁.bot = s₁.top := congr_arg s₁ (Fin.ext (by simp [hs₁]))
  have : Fin.last s₂.length = (0 : Fin s₂.length.succ) :=
    s₂.injective (hb.symm.trans (this.trans ht)).symm
  -- Porting note: Was `simpa [Fin.ext_iff]`.
  rw [Fin.ext_iff] at this
  simpa

theorem length_pos_of_bot_eq_bot_of_top_eq_top_of_length_pos {s₁ s₂ : StrictSeries X}
    (hb : s₁.bot = s₂.bot) (ht : s₁.top = s₂.top) : 0 < s₁.length → 0 < s₂.length :=
  not_imp_not.1
    (by
      simp only [pos_iff_ne_zero, Ne.def, not_iff_not, Classical.not_not]
      exact length_eq_zero_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero hb.symm ht.symm)

theorem eq_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero {s₁ s₂ : StrictSeries X}
    (hb : s₁.bot = s₂.bot) (ht : s₁.top = s₂.top) (hs₁0 : s₁.length = 0) : s₁ = s₂ := by
  have : ∀ x, x ∈ s₁ ↔ x = s₁.top := fun x =>
    ⟨fun hx => forall_mem_eq_of_length_eq_zero hs₁0 hx s₁.top_mem, fun hx => hx.symm ▸ s₁.top_mem⟩
  have : ∀ x, x ∈ s₂ ↔ x = s₂.top := fun x =>
    ⟨fun hx =>
      forall_mem_eq_of_length_eq_zero
        (length_eq_zero_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero hb ht hs₁0) hx s₂.top_mem,
      fun hx => hx.symm ▸ s₂.top_mem⟩
  ext
  simp [*]

end Preorder

end StrictSeries
