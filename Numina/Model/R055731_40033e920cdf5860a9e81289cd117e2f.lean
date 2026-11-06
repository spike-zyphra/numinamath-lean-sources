import Mathlib

theorem algebra_19811 {d c : ℝ} (h₀ : d - 6 * c = 4) (h₁ : 2 * d - 9 * c = 20) :
    d / c = 7 := by
  have hc : c ≠ 0 := by
    by_contra h'
    rw [h'] at h₀ h₁
    linarith
  have eq1 : 2 * d - 12 * c = 8 := by
    linarith [h₀]
  have hc' : c = 4 := by
    linarith [eq1, h₁]
  have hd : d = 28 := by
    rw [hc'] at h₀
    linarith
  have h2 : d / c = 7 := by
    rw [hd, hc']
    all_goals norm_num
  exact h2