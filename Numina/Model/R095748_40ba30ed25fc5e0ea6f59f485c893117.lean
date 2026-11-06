import Mathlib

theorem calculus_14757 (m b : ℝ) (h : ∀ x y, (1 * x + 3 * y - 1 * (-2) - 3 * 8) = 0 → y = m * x + b) :
    m = -1 / 3 ∧ b = 22 / 3 := by 
  have eq1 := h (-2) 8 (by norm_num)
  have eq2 := h 1 7 (by norm_num)
  have h1 : 8 = m * (-2) + b := by
    linarith
  have h2 : 7 = m + b := by
    linarith
  have hm : m = -1 / 3 := by
    linarith [h1, h2]
  have hb : b = 22 / 3 := by 
    rw [hm] at h2
    linarith
  exact ⟨hm, hb⟩