import Mathlib

theorem algebra_3746 {a b c : ℝ} (ha : a ≠ 0) (f : ℝ → ℝ) (hf : ∀ x, f x = a * x ^ 2 + b * x + c) (h1 : f 1 = -6) (h2 : f 2 = -3) (h3 : f 3 = 4) : f 4 = 15 := by
  have eq1 : a + b + c = -6 := by
    rw [hf] at h1
    linarith
  have eq2 : 4 * a + 2 * b + c = -3 := by
    rw [hf] at h2
    norm_num at h2
    linarith
  have eq3 : 9 * a + 3 * b + c = 4 := by
    rw [hf] at h3
    norm_num at h3
    linarith
  have eq4 : 3 * a + b = 3 := by
    linarith [eq1, eq2]
  have eq5 : 5 * a + b = 7 := by
    linarith [eq2, eq3]
  have ha2 : a = 2 := by
    linarith [eq4, eq5]
  have h2b : b = -3 := by
    linarith [eq4, ha2]
  have h2c : c = -5 := by
    linarith [eq1, ha2, h2b]
  have eq4_val : f 4 = a * 4 ^ 2 + b * 4 + c := hf 4
  rw [eq4_val]
  rw [ha2, h2b, h2c]
  norm_num