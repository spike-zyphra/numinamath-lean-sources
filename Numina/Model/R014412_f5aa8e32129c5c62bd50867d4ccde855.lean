import Mathlib

theorem algebra_142160 {f : ℝ → ℝ} (hf : ∃ a b c, a < 0 ∧ ∀ x, f x = a * x ^ 2 + b * x + c)
    (h : ∀ x, f (x + 2) = f (2 - x)) :
    f (-1992) < f 1992 ∧ f 1992 < f 0 := by
  rcases hf with ⟨a, b, c, ha, hf⟩
  have h2 := h 1
  simp [hf] at h2
  have h3 : b = -4 * a := by
    nlinarith
  have h4 : f (-1992) = a * (-1992) ^ 2 + b * (-1992) + c := hf (-1992)
  have h5 : f 1992 = a * 1992 ^ 2 + b * 1992 + c := hf 1992
  have h6 : f (0) = c := by
    specialize hf 0
    norm_num at hf ⊢
    linarith
  have eq1 : f (-1992) = a * (-1992) ^ 2 + (-4 * a) * (-1992) + c := by
    rw [h4, h3]
  have eq2 : f 1992 = a * 1992 ^ 2 + (-4 * a) * 1992 + c := by
    rw [h5, h3]
  have h7 : f (-1992) < f 1992 := by
    rw [eq1, eq2]
    nlinarith [ha, show (1992 : ℝ) > 0 by norm_num]
  have h8 : f 1992 < f 0 := by
    rw [eq2, h6]
    nlinarith [ha, show (1992 : ℝ) > 0 by norm_num]
  exact ⟨h7, h8⟩