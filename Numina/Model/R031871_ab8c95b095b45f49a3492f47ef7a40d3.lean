import Mathlib

theorem algebra_4450 {a b c : ℝ} (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (h1 : a * b + b * c + c * a = 33) (h2 : a ^ 2 + b ^ 2 + c ^ 2 = 42) :
    a + b + c = 6 * Real.sqrt 3 := by
  have h3 : (a + b + c) ^ 2 = 108 := by
    calc
      (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a) := by ring
      _ = 42 + 2 * 33 := by rw [h2, h1]
      _ = 108 := by norm_num
  have h4 : a + b + c > 0 := by
    linarith
  have h7 : a + b + c = Real.sqrt 108 := by
    have h6 : Real.sqrt ((a + b + c) ^ 2) = a + b + c := by
      rw [Real.sqrt_sq (show 0 ≤ a + b + c by linarith)]
    have h5 : Real.sqrt ((a + b + c) ^ 2) = Real.sqrt 108 := by
      rw [h3]
    linarith [h6, h5]
  have h8 : Real.sqrt 108 = 6 * Real.sqrt 3 := by
    calc
      Real.sqrt 108 = Real.sqrt (6 ^ 2 * (3 : ℝ)) := by norm_num
      _ = (6 : ℝ) * Real.sqrt (3 : ℝ) := by 
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [h7, h8]
  all_goals linarith