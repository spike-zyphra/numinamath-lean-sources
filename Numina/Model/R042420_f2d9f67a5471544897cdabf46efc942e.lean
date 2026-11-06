import Mathlib

theorem calculus_18627 (l : ℝ → ℝ × ℝ) (a d : ℝ × ℝ) (h0 : ∀ t, l t = a + t • d) (h1 : l (-2) = (2, -4)) (h2 : l 3 = (1, 7)) : l 5 = (3 / 5, 57 / 5) := by
  have eq1 := h0 (-2)
  rw [eq1] at h1
  have eq2 := h0 3
  rw [eq2] at h2
  have eq3 := h0 5
  have h3 : a.1 + (-2) * d.1 = 2 := by
    simp [Prod.ext_iff] at h1 ⊢
    linarith
  have h4 : a.2 + (-2) * d.2 = -4 := by
    simp [Prod.ext_iff] at h1 ⊢
    linarith
  have h5 : a.1 + 3 * d.1 = 1 := by
    simp [Prod.ext_iff] at h2 ⊢
    linarith
  have h6 : a.2 + 3 * d.2 = 7 := by
    simp [Prod.ext_iff] at h2 ⊢
    linarith
  have ha1 : a.1 = 8 / 5 := by
    linarith
  have ha2 : a.2 = 2 / 5 := by
    linarith
  have hd1 : d.1 = -1 / 5 := by
    linarith
  have hd2 : d.2 = 11 / 5 := by
    linarith
  rw [h0 5]
  simp [Prod.ext_iff, ha1, ha2, hd1, hd2]
  all_goals norm_num