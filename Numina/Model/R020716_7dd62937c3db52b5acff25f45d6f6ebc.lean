import Mathlib

theorem algebra_11181 {a b c : ℝ} (ha : a = 4) (hb : b = 9) (hc : c = 36)
    (r : ℝ) (hr : r > 0) :
    1 / r = 1 / a + 1 / b + 1 / c + 2 * √(1 / (a * b) + 1 / (a * c) + 1 / (b * c)) ↔
    r = 9 / 7 := by
  constructor
  · -- Assume 1 / r = 1 / a + 1 / b + 1 / c + 2 * √(1 / (a * b) + 1 / (a * c) + 1 / (b * c)), prove r = 9 / 7
    intro h_eq
    have ha' : a = 4 := ha
    have hb' : b = 9 := hb
    have hc' : c = 36 := hc
    rw [ha'] at h_eq
    rw [hb'] at h_eq
    rw [hc'] at h_eq
    have h1 : 1 / r = 1 / (4 : ℝ) + 1 / (9 : ℝ) + 1 / (36 : ℝ) + 2 * √(1 / ((4 : ℝ) * 9) + 1 / ((4 : ℝ) * 36) + 1 / ((9 : ℝ) * 36)) := by
      simpa using h_eq
    have h2 : 1 / r = (7 : ℝ) / 9 := by
      have h3 : 1 / (4 : ℝ) + 1 / (9 : ℝ) + 1 / (36 : ℝ) = (7 : ℝ) / 18 := by norm_num
      have h4 : (1 / ((4 : ℝ) * 9) + 1 / ((4 : ℝ) * 36) + 1 / ((9 : ℝ) * 36) : ℝ) = (49 : ℝ) / 1296 := by norm_num
      rw [h3, h4] at h1
      have h5 : √((49 : ℝ) / 1296) = (7 : ℝ) / 36 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h5] at h1
      linarith
    have h3 : r = 9 / 7 := by
      field_simp at h2 ⊢
      nlinarith
    exact h3
  · -- Assume r = 9 / 7, prove the equation
    intro h_eq
    have ha' : a = 4 := ha
    have hb' : b = 9 := hb
    have hc' : c = 36 := hc
    rw [ha']
    rw [hb']
    rw [hc']
    rw [show r = (9 : ℝ) / 7 by linarith [h_eq]]
    have h1 : 1 / ((9 : ℝ) / 7) = (7 : ℝ) / 9 := by
      field_simp
    have h3 : (1 / (4 : ℝ) + 1 / (9 : ℝ) + 1 / (36 : ℝ) : ℝ) = (7 : ℝ) / 18 := by norm_num
    have h4 : (1 / ((4 : ℝ) * 9) + 1 / ((4 : ℝ) * 36) + 1 / ((9 : ℝ) * 36) : ℝ) = (49 : ℝ) / 1296 := by norm_num
    have h5 : √((1 / ((4 : ℝ) * 9) + 1 / ((4 : ℝ) * 36) + 1 / ((9 : ℝ) * 36) : ℝ)) = (7 : ℝ) / 36 := by
      rw [h4]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1]
    rw [h3, h5]
    all_goals norm_num
    all_goals linarith