import Mathlib

theorem algebra_181006 (f : ℝ → ℝ) (hf : f = fun x => x^2 - x + 5.35) :
    ¬∃ x, f x = 2 * Real.sin x + 3 := by 
  rintro ⟨x, hx⟩ 
  rw [hf] at hx
  simp at hx
  have h1 : (x ^ 2 - x + (5.35 : ℝ)) ≥ 5.1 := by
    have h2 : (x - (0.5 : ℝ)) ^ 2 ≥ 0 := sq_nonneg (x - 0.5)
    ring_nf at h2 ⊢
    linarith
  have h2 : 2 * Real.sin x + 3 ≤ 5 := by
    have h3 : Real.sin x ≤ 1 := Real.sin_le_one x
    linarith
  linarith [h1, hx, h2]