import Mathlib

theorem algebra_3058 {a b : ℝ} (h : abs (a - 3) + (b + 15) ^ 4 = 0) : 7 * a + 17 * b = -234 := by
  have h1 : abs (a - 3) ≥ 0 := by 
    apply abs_nonneg
  have h2 : (b + 15) ^ 4 ≥ 0 := by
    positivity
  have h3 : abs (a - 3) = 0 := by
    linarith
  have ha : a - 3 = 0 := by
    rw [abs_eq_zero] at h3
    linarith
  have ha' : a = 3 := by
    linarith
  have h4 : (b + 15) ^ 4 = 0 := by 
    linarith
  have hb : b + 15 = 0 := by
    apply pow_eq_zero 
    exact h4
  have hb' : b = -15 := by
    linarith
  rw [ha', hb']
  norm_num