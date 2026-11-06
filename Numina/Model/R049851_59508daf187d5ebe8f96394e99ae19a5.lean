import Mathlib

theorem algebra_291262 (a b c : ℝ) (ha : a ≠ 0) (f : ℝ → ℝ)
    (hf : ∀ x, f x = a * x * Real.sqrt (x - 1) + b * x + c)
    (h1 : 0 < 2 * f 5) (h2 : 2 * f 5 = 3 * f 10) (h3 : 3 * f 10 = 4 * f 17)
    (h4 : 4 * f 17 ≤ 1) :
    a ≤ 3 / 200 := by
  have eq1 : f 5 = a * 5 * Real.sqrt (5 - 1) + b * 5 + c := hf 5
  have eq2 : f 10 = a * 10 * Real.sqrt (10 - 1) + b * 10 + c := hf 10
  have eq3 : f 17 = a * 17 * Real.sqrt (17 - 1) + b * 17 + c := hf 17

  have sqrt_4 : Real.sqrt (5 - 1 : ℝ) = 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num

  have sqrt_9 : Real.sqrt (10 - 1 : ℝ) = 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num

  have sqrt_16 : Real.sqrt (17 - 1 : ℝ) = 4 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num

  rw [sqrt_4] at eq1
  rw [sqrt_9] at eq2
  rw [sqrt_16] at eq3

  have eq_f5 : f 5 = 10 * a + 5 * b + c := by
    linarith [eq1]

  have eq_f10 : f 10 = 30 * a + 10 * b + c := by
    linarith [eq2]

  have eq_f17 : f 17 = 68 * a + 17 * b + c := by
    linarith [eq3]

  rw [eq_f5] at h1 h2
  rw [eq_f10] at h2 h3
  rw [eq_f17] at h3 h4

  linarith