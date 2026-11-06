import Mathlib

/- In a Martian civilization, all logarithms whose bases are not specified are assumed to be base
b, for some fixed b≥2 . A Martian student writes down
3 log (sqrt(x) * log x) = 56
log_(log x) (x) = 54
and finds that this system of equations has a single real number solution x > 1. Find b. -/


theorem algebra_98011 (x b : ℝ) (hx : x > 1) (hb: b ≥ 2)
(h1 : 3 * Real.logb b (Real.sqrt x * Real.logb b x) = 56)
(h2 : Real.logb (Real.logb b x) x = 54) (h2' : 0 < Real.logb b x) (h2'': Real.logb b x ≠ 1)
: b = 216 := by
  -- first define bunch of 0 <, 0 ≤, ≠ 1 as those are required in log problems
  have h_b_nn : 0 ≤ b := by linarith
  have h_b_p : 0 < b := by linarith
  have h_b_no : b ≠ 1 := by linarith
  have h_x_p : 0 < x := by linarith
  have h2''' : 0 ≤ Real.logb b x := by linarith
  -- using second equation determine log_b(x)^54 = x
  have h2: (Real.logb b x)^(54:ℝ) = x := by
    exact (Real.logb_eq_iff_rpow_eq h2' h2'' h_x_p).mp h2
  nth_rw 1 [← h2] at h1
  -- a simple lemma to convert √(y^54) = y^27
  have {y : ℝ} (h: 0 ≤ y) : √ (y^(54:ℝ)) = y^(27:ℝ) := by
    calc
      √ (y^ (54:ℝ)) = √ (y^((27:ℝ)*2)) := by norm_num
      _ = √ ((y^(27:ℝ))^2) := by
        rw [Real.rpow_mul h (27:ℝ) (2:ℝ)]
        norm_cast
      _ = y^(27:ℝ) := by
        norm_cast
        apply Real.sqrt_sq (pow_nonneg h 27)
  -- now convert  3 * Real.logb b (√(Real.logb b x ^ 54) * Real.logb b x) = 56 to Real.logb b (Real.logb b x ^ 28) * 3 = 56
  rw [this h2'''] at h1
  norm_cast at h1
  ring_nf at h1
  -- from last equation determine  54 * Real.logb b (Real.logb b x) = 54 * 56 / 84
  have (x : ℝ) : x ^ (28:ℝ)  = x ^ 28 := by norm_cast
  rw [← this (Real.logb b x) , Real.logb_rpow_eq_mul_logb_of_pos h2'] at h1
  have h1: 54 * Real.logb b (Real.logb b x) = 54 * 56 / 84 := by linarith
  -- use the fact that Real.logb b x ^ 54 = x to simplify to Real.logb b x = 54 * 56 / 84
  rw [← Real.logb_rpow_eq_mul_logb_of_pos h2', h2] at h1
  norm_num at h1
  -- this means Real.logb b x)^54 = 36^54, which means b^36 = x, using this at log_b(x)^54 = x gives x = 36^54
  have hx' : (Real.logb b x)^(54:ℝ) = 36^(54:ℝ) := by rw [h1]
  rw [h2] at hx'
  have hx'': b^(36:ℝ) = x := by
    exact (Real.logb_eq_iff_rpow_eq h_b_p h_b_no h_x_p).mp h1
  -- eliminate x to get b ^ 36 = 36 ^ 54, which implies x= 216
  rw [hx'] at hx''
  norm_cast at hx''
  have : (↑((36:ℕ)^54):ℝ) = (216:ℝ) ^36 := by norm_num
  rw [this] at hx''
  exact (pow_left_inj₀ h_b_nn (by norm_num) (by norm_num)).mp hx''