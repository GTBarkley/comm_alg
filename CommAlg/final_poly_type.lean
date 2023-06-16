import Mathlib.Order.Height
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic

-- Setting for "library_search"
set_option maxHeartbeats 0
macro "ls" : tactic => `(tactic|library_search)

-- From Kyle : New tactic "obviously"
macro "obviously" : tactic =>
  `(tactic| (
      first
        | dsimp; simp; done; dbg_trace "it was dsimp simp"
        | simp; done; dbg_trace "it was simp"
        | tauto; done; dbg_trace "it was tauto"
        | simp; tauto; done; dbg_trace "it was simp tauto"
        | rfl; done; dbg_trace "it was rfl"
        | norm_num; done; dbg_trace "it was norm_num"
        | norm_cast; done; dbg_trace "it was norm_cast"
        | /-change (@Eq ℝ _ _);-/ linarith; done; dbg_trace "it was linarith"
        -- | gcongr; done
        | ring; done; dbg_trace "it was ring"
        | trivial; done; dbg_trace "it was trivial"
        -- | nlinarith; done
        | fail "No, this is not obvious."))

-- Testing of Polynomial
section Polynomial
noncomputable section

example (f : Polynomial ℚ) (hf : f = Polynomial.C (1 : ℚ)) : Polynomial.eval 2 f = 1 := by
  have : ∀ (q : ℚ), Polynomial.eval q f = 1 := by
    sorry

-- degree of a constant function is ⊥ (is this same as -1 ???)
#print Polynomial.degree_zero

def F : Polynomial ℚ := Polynomial.C (2 : ℚ)

-- #eval Polynomial.degree F
example : Polynomial.eval (100 : ℚ) F = (2 : ℚ) := by
  refine Iff.mpr (Rat.ext_iff (Polynomial.eval 100 F) 2) ?_
  simp only [Rat.ofNat_num, Rat.ofNat_den]
  rw [F]
  simp [simp]

-- Treat polynomial f ∈ ℚ[X] as a function f : ℚ → ℚ

end section

-- All the polynomials are in ℚ[X], all the functions are considered as ℤ → ℤ
noncomputable section
-- Polynomial type of degree d
@[simp]
def PolyType (f : ℤ → ℤ) (d : ℕ) := 
  ∃ Poly : Polynomial ℚ, ∃ (N : ℤ), (∀ (n : ℤ), N ≤ n → f n = Polynomial.eval (n : ℚ) Poly) ∧ 
    d = Polynomial.degree Poly
section

example (f : ℤ → ℤ) (hf : ∀ x, f x = x ^ 2) : PolyType f 2 := by
  unfold PolyType
  sorry
 
end section

-- Δ operator (of d times)
@[simp]
def Δ : (ℤ → ℤ) → ℕ → (ℤ → ℤ)
  | f, 0 => f
  | f, d + 1 => fun (n : ℤ) ↦ (Δ f d) (n + 1) - (Δ f d) (n)  

-- (NO need to prove another direction) Constant polynomial function = constant function
lemma Poly_constant (F : Polynomial ℚ) (c : ℚ) : 
    (F = Polynomial.C (c : ℚ)) ↔ (∀ r : ℚ, (Polynomial.eval r F) = (c : ℚ)) := by
  constructor
  · intro h r
    refine Iff.mpr (Rat.ext_iff (Polynomial.eval r F) c) ?_
    simp only [Rat.ofNat_num, Rat.ofNat_den]
    simp [h]
  · sorry

-- Get the polynomial G (X) = F (X + s) from the polynomial F(X)
lemma Polynomial_shifting (F : Polynomial ℚ) (s : ℚ) : ∃ (G : Polynomial ℚ), (∀ (x : ℚ), Polynomial.eval x G = Polynomial.eval (x + s) F) ∧ (Polynomial.degree G = Polynomial.degree F) := by  
  sorry

-- Shifting doesn't change the polynomial type
lemma Poly_shifting (f : ℤ → ℤ) (g : ℤ → ℤ) (hf : PolyType f d) (s : ℕ) 
    (hfg : ∀ (n : ℤ), f (n + s) = g (n)) : PolyType g d := by
  rcases hf with ⟨F, ⟨N, s1, s2⟩⟩
  rcases (Polynomial_shifting F s) with ⟨Poly, h1, h2⟩
  use Poly, N; constructor
  · intro n hN
    have this1 : f (n + s) = Polynomial.eval (n + (s : ℚ)) F := by
      rw [s1 (n + s) (by linarith)]; norm_cast
    rw [←hfg n, this1]; exact (h1 n).symm
  · rw [h2, s2]

-- PolyType 0 = constant function
lemma PolyType_0 (f : ℤ → ℤ) : (PolyType f 0) ↔ (∃ (c : ℤ), ∃ (N : ℤ), (∀ (n : ℤ), 
    (N ≤ n → f n = c)) ∧ c ≠ 0) := by
  constructor
  · rintro ⟨Poly, ⟨N, ⟨H1, H2⟩⟩⟩ 
    have this1 : Polynomial.degree Poly = 0 := by rw [← H2]; rfl
    have this2 : ∃ (c : ℤ), Poly = Polynomial.C (c : ℚ) := by
      have HH : ∃ (c : ℚ), Poly = Polynomial.C (c : ℚ) := 
        ⟨Poly.coeff 0, Polynomial.eq_C_of_degree_eq_zero (by rw[← H2]; rfl)⟩
      cases' HH with c HHH
      have HHHH : ∃ (d : ℤ), d = c :=
        ⟨f N, by simp [(Poly_constant Poly c).mp HHH N, H1 N (le_refl N)]⟩
      cases' HHHH with d H5; exact ⟨d, by rw[← H5] at HHH; exact HHH⟩
    rcases this2 with ⟨c, hthis2⟩ 
    use c; use N; constructor
    · intro n
      have this4 : Polynomial.eval (n : ℚ) Poly = c := by
        rw [hthis2]; simp only [map_intCast, Polynomial.eval_int_cast]
      exact fun HH1 => Iff.mp (Rat.coe_int_inj (f n) c) (by rw [←this4, H1 n HH1])
    · intro c0
      simp only [hthis2, c0, Int.cast_zero, map_zero, Polynomial.degree_zero] 
        at this1
  · rintro ⟨c, N, hh⟩
    have H2 : (c : ℚ) ≠ 0 := by simp only [ne_eq, Int.cast_eq_zero, hh]
    exact ⟨Polynomial.C (c : ℚ), N, fun n Nn 
      => by rw [hh.1 n Nn]; exact (((Poly_constant (Polynomial.C (c : ℚ)) 
      (c : ℚ)).mp rfl) n).symm, by rw [Polynomial.degree_C H2]; rfl⟩

-- Δ of 0 times preserves the function
lemma Δ_0 (f : ℤ → ℤ) : (Δ f 0) = f := by rfl

-- Δ of 1 times decreaes the polynomial type by one --can be golfed
lemma Δ_1 (f : ℤ → ℤ) (d : ℕ) : PolyType f (d + 1) → PolyType (Δ f 1) d := by
  intro h
  simp only [PolyType, Δ, Int.cast_sub, exists_and_right]
  rcases h with ⟨F, N, h⟩
  rcases h with ⟨h1, h2⟩
  have this : ∃ (G : Polynomial ℚ), (∀ (x : ℚ), Polynomial.eval x G = Polynomial.eval (x + 1) F) ∧ (Polynomial.degree G = Polynomial.degree F) := by
    exact Polynomial_shifting F 1
  rcases this with ⟨G, hG, hGG⟩
  let Poly := G - F
  use Poly
  constructor
  · use N
    intro n hn
    specialize hG n
    norm_num
    rw [hG]
    let h3 := h1
    specialize h3 n
    have this1 : f n = Polynomial.eval (n : ℚ) F := by tauto
    have this2 : f (n + 1) = Polynomial.eval ((n + 1) : ℚ) F := by
      specialize h1 (n + 1)
      have this3 : N ≤ n + 1 := by linarith
      aesop
    rw [←this1, ←this2]
  · have this1 : Polynomial.degree Poly = d := by
      have this2 : Polynomial.degree Poly ≤ d := by
        sorry
      have this3 : Polynomial.degree Poly ≥ d := by
        sorry
      sorry
    tauto

-- Δ of d times maps polynomial of degree d to polynomial of degree 0
lemma Δ_1_s_equiv_Δ_s_1 (f : ℤ → ℤ) (s : ℕ) : Δ (Δ f 1) s = (Δ f (s + 1)) := by
  induction' s with s hs
  · norm_num
  · aesop

lemma foofoo (d : ℕ) : (f : ℤ → ℤ) → (PolyType f d) → (PolyType (Δ f d) 0):= by
  induction' d with d hd
  · intro f h
    rw [Δ_0]
    exact h
  · intro f hf
    have this4 := hd (Δ f 1) $ (Δ_1 f d) hf
    rwa [Δ_1_s_equiv_Δ_s_1] at this4

lemma Δ_d_PolyType_d_to_PolyType_0 (f : ℤ → ℤ) (d : ℕ): PolyType f d → PolyType (Δ f d) 0 := 
  fun h => (foofoo d f) h

-- The "reverse" of Δ of 1 times increases the polynomial type by one
lemma Δ_1_ (f : ℤ → ℤ) (d : ℕ) : PolyType (Δ f 1) d → PolyType f (d + 1) := by
  rintro ⟨P, N, ⟨h1, h2⟩⟩ 
  simp only [PolyType, Nat.cast_add, Nat.cast_one, exists_and_right]
  let G := fun (q : ℤ) => f (N)
  sorry

lemma foo (d : ℕ) : (f : ℤ → ℤ) → (∃ (c : ℤ), ∃ (N : ℤ), (∀ (n : ℤ), N ≤ n → 
    (Δ f d) (n) = c) ∧ c ≠ 0) → (PolyType f d)  := by
  induction' d with d hd
  · rintro f ⟨c, N, hh⟩; rw [PolyType_0 f]; exact ⟨c, N, hh⟩
  · exact fun f ⟨c, N, ⟨H, c0⟩⟩ =>
      Δ_1_ f d (hd (Δ f 1) ⟨c, N, fun n h => by rw [← H n h, Δ_1_s_equiv_Δ_s_1], c0⟩)

-- [BH, 4.1.2] (a) => (b)
-- Δ^d f (n) = c for some nonzero integer c for n >> 0 → f is of polynomial type d
lemma a_to_b (f : ℤ → ℤ) (d : ℕ) : (∃ (c : ℤ), ∃ (N : ℤ), (∀ (n : ℤ), N ≤ n → (Δ f d) (n) = c) ∧ c ≠ 0) → PolyType f d := fun h => (foo d f) h

-- [BH, 4.1.2] (a) <= (b)
-- f is of polynomial type d → Δ^d f (n) = c for some nonzero integer c for n >> 0
lemma b_to_a (f : ℤ → ℤ) (d : ℕ) (poly : PolyType f d) : 
    (∃ (c : ℤ), ∃ (N : ℤ), (∀ (n : ℤ), N ≤ n → (Δ f d) (n) = c) ∧ c ≠ 0) := by
  rw [←PolyType_0]; exact Δ_d_PolyType_d_to_PolyType_0 f d poly

end

-- @Additive lemma of length for a SES
-- Given a SES 0 → A → B → C → 0, then length (A) - length (B) + length (C) = 0 
section
open LinearMap

-- Definitiion of the length of a module
noncomputable def length (R M : Type _) [CommRing R] [AddCommGroup M] [Module R M] := Set.chainHeight {M' : Submodule R M | M' < ⊤}
#check length ℤ ℤ

-- Definition of a SES (Short Exact Sequence)
-- @[ext]
structure SES {R A B C : Type _} [CommRing R] [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C] [Module R A] [Module R B] [Module R C] 
  (f : A →ₗ[R] B) (g : B →ₗ[R] C)
  where
  left_exact : LinearMap.ker f = ⊥
  middle_exact : LinearMap.range f = LinearMap.ker g
  right_exact : LinearMap.range g = ⊤

-- Additive lemma
lemma length_Additive (R A B C : Type _) [CommRing R] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module R A] [Module R B] [Module R C] 
  (f : A →ₗ[R] B) (g : B →ₗ[R] C)
  : (SES f g) → ((length R A) + (length R C) = (length R B)) := by
  intro h
  rcases h with ⟨left_exact, middle_exact, right_exact⟩
  sorry

end section