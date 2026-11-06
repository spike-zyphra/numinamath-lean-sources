import Mathlib
open Real

theorem algebra_610648 {x y z : ℝ} (hx : 1 < x) (hy : 1 < y) (hz : 1 < z) (h1: x ^ (logb y z) = 2) (h2: y ^ (logb z x) = 4) (h3: z ^ (logb x y) = 8) : (logb x y = sqrt 3) := by
  have hxp: log x > 0 := by
       apply log_pos; exact hx
  have hyp: log y > 0 := by
       apply log_pos; exact hy
  have hzp: log z > 0 := by
       apply log_pos; exact hz

  have h1' : logb y z * log x = log 2 := by
    have h11 : log (x ^ (logb y z)) = log 2 := by rw [h1]
    have h12 : log (x ^ (logb y z)) = logb y z * log x := by
      field_simp [log_rpow]
    linarith

  have h2' : logb z x * log y = log 4 := by
    have h21 : log (y ^ (logb z x)) = log 4 := by rw [h2]
    have h22 : log (y ^ (logb z x)) = logb z x * log y := by
      field_simp [log_rpow]
    linarith

  have h3' : logb x y * log z = log 8 := by
    have h31 : log (z ^ (logb x y)) = log 8 := by rw [h3]
    have h32 : log (z ^ (logb x y)) = logb x y * log z := by
      field_simp [log_rpow]
    linarith

  have h1'' : (log z / log y) * log x = log 2 := by
    have h4 : logb y z = log z / log y := by
      field_simp [logb]
    rw [h4] at h1'
    linarith

  have h2'' : (log x / log z) * log y = log 4 := by
    have h5 : logb z x = log x / log z := by
      field_simp [logb]
    rw [h5] at h2'
    linarith

  have h3'' : (log y / log x) * log z = log 8 := by
    have h6 : logb x y = log y / log x := by
      field_simp [logb]
    rw [h6] at h3'
    linarith

  have h4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    simp [log_pow]

  have h5 : log 8 = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num]
    simp [log_pow]

  rw [h4] at h2''

  rw [h5] at h3''

  have h8 : (log y / log x) ^ 2 = 3 := by
    have h9 : (log z / log y) * log x = log 2 := by
      linarith
    have h10 : (log x / log z) * log y = 2 * log 2 := by
      linarith
    have h11 : (log y / log x) * log z = 3 * log 2 := by
      linarith
    -- introduce variables to simplify the system
    -- a = log x, b = log y, c = log z
    -- with the equations:
    -- (c / b) * a = log 2
    -- (a / c) * b = 2 * log 2
    -- (b / a) * c = 3 * log 2
    -- solve to get (b / a) ^ 2 = 3
    have h12 : log z * log x = log 2 * log y := by
      field_simp [show log y ≠ 0 by linarith] at h9 ⊢
      nlinarith

    have h13 : (log y / log x) ^ 2 = 3 := by
      -- square both sides
      -- (log y / log x)^2 * (log x)^2 = (3 * log 2)^2 / (log x)^2 * (log x)^2
      -- (log y)^2 * (log x)^2 / (log x)^2 = 9 * (log 2)^2
      -- (log y)^2 = 9 * (log 2)^2 / 1
      -- no, right way is:
      -- We have a * b * c = 6 * (log 2)^3
      -- For time constraints, Lean 4's nonlinear arithmetic is really helpful here
      field_simp [show log x ≠ 0 by linarith] at *
      nlinarith [sq_pos_of_pos hxp, sq_pos_of_pos hyp, sq_pos_of_pos hzp, h12]

    exact h13

  have h9 : logb x y = log y / log x := by
    field_simp [logb]

  rw [h9]

  have h10 : log y / log x = Real.sqrt 3 := by
    have h11 : log y / log x ≥ 0 := by
      apply div_nonneg
      linarith
      linarith
    have h12 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
    have h13 : (log y / log x) = Real.sqrt 3 := by
      nlinarith [h8, Real.sqrt_nonneg 3, h12, h11]
    exact h13

  linarith [h10]