import Mathlib

-- Define function f : ℤ × ℤ → ℤ
def f (x y : ℤ) : ℤ := x^3 - 3 * x * y^2 + y^3

-- Define the corresponding version in ZMod 9
def f_mod (x y : ZMod 9) : ZMod 9 :=
  x^3 - 3 * x * y^2 + y^3

theorem Combinatorics_5659
    (S : Finset (ℤ × ℤ))
    (n : ℤ)
    (h₀ : n > 0)
    (h₁ : ∃ x y : ℤ, f x y = n ∧ (x, y) ∈ S)
    (h₂ : ∀ x y : ℤ, (x, y) ∈ S ↔ f x y = n) : 
    2 < S.card  ∧ ¬ ∃ x y : ℤ, f x y = 2891 := by
  apply And.intro
  obtain ⟨x, y, h₄, h₅⟩ := h₁
  apply Finset.two_lt_card_iff.mpr
  use (x, y), (y-x, -x), (-y, x-y)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_ ⟩ 
    -- verifying that the solutions are in S
  · exact h₅ 
    -- verifying that the solutions are in S
  · rw [h₂] 
    rw [← h₄, f, f]
    ring
    -- verifying that the solutions are in S
  · rw [h₂] 
    rw [← h₄, f, f]
    ring
    --show three solutions are unique 
  · simp
    intros tmp tmp1
    replace tmp : y = 0 := by linarith
    replace tmp1 : x = 0 := by linarith
    rw [f, tmp, tmp1] at h₄ 
    simp_all
  · --show three solutions are unique 
    simp
    intros tmp tmp1
    replace tmp : y = 0 := by linarith
    replace tmp1 : x = 0 := by linarith
    rw [f, tmp, tmp1] at h₄ 
    simp_all
  · --show three solutions are unique 
    simp
    intros tmp tmp1
    replace tmp : y = 0 := by linarith
    replace tmp1 : x = 0 := by linarith
    rw [f, tmp, tmp1] at h₄ 
    simp_all
  · rintro ⟨x, y, h⟩
    -- reduce 2891 to mod 9 using a brute-force check (ZMod 9 is finite)
    have hmod : (f x y : ZMod 9) = 2 := by rw[h]; decide
    have : f_mod (x : ZMod 9) (y : ZMod 9) = 2 := by
      simp [f_mod, f]
      norm_cast
    -- Show that f_mod x y ≠ 2 for all x y : ZMod 9
    have f_mod_ne_2 : ∀ x y : ZMod 9, f_mod x y ≠ 2 := by decide
    --derive a contradiction
    exact f_mod_ne_2 (x : ZMod 9) (y : ZMod 9) this