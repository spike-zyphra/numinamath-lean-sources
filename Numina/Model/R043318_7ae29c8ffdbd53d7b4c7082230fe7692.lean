import Mathlib

theorem algebra_178024 (f : ℝ → ℝ) (hf : f = fun x => x ^ 2) (c : ℝ) (hc : c > 0)
    (h : ∃ x1 x2, x1 ≠ x2 ∧ f x1 = c ∧ f x2 = c - 2) :
    c > 5 / 4 := by
  rcases h with ⟨x1, x2, hx1x2, hfx1, hfx2⟩
  have eq1 : x1 ^ 2 = c := by
    rw [hf] at hfx1
    simp at hfx1
    linarith
  have eq2 : x2 ^ 2 = c - 2 := by
    rw [hf] at hfx2
    simp at hfx2
    linarith
  have h2 : c - 2 ≥ 0 := by
    have h3 : x2 ^ 2 ≥ 0 := by
      apply sq_nonneg
    linarith [eq2, h3]
  have h3 : c ≥ 2 := by
    linarith
  linarith