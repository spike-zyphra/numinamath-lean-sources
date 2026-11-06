import Mathlib

theorem algebra_213757 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h : a^2 + b^2 = c^2) (h1 : Real.log (a + b) = (Real.log b + Real.log (a + 3 * b)) / 2) :
    Real.arctan (a / b) = Real.pi / 4 := by
  have h2 : Real.log (a + b) = (1 / 2) * (Real.log b + Real.log (a + 3 * b)) := by
    linarith [h1]
  have h3 : Real.log b + Real.log (a + 3 * b) = Real.log (b * (a + 3 * b)) := by
    rw [Real.log_mul (by positivity) (by positivity)]
  have h4 : Real.log (a + b) = (1 / 2) * Real.log (b * (a + 3 * b)) := by
    rw [h3] at h2
    linarith
  have h5 : a + b > 0 := by positivity
  have h6 : b * (a + 3 * b) > 0 := by positivity
  have h7 : Real.log (a + b) = Real.log ((b * (a + 3 * b)) ^ (1 / 2 : ℝ)) := by
    rw [h4]
    have h8 : Real.log ((b * (a + 3 * b)) ^ (1 / 2 : ℝ)) = (1 / 2 : ℝ) * Real.log (b * (a + 3 * b)) := by
      rw [Real.log_rpow]
      all_goals nlinarith
    linarith [h8]
  have h8 : (a + b) = (b * (a + 3 * b)) ^ (1 / 2 : ℝ) := by
    have h7' : Real.log (a + b) = Real.log ((b * (a + 3 * b)) ^ (1 / 2 : ℝ)) := h7
    have h9 : (a + b) > 0 := by positivity
    have h10 : (b * (a + 3 * b)) ^ (1 / 2 : ℝ) > 0 := by positivity
    have h11 : (a + b) = (b * (a + 3 * b)) ^ (1 / 2 : ℝ) := by
      apply Real.log_injOn_pos (Set.mem_Ioi.mpr h9) (Set.mem_Ioi.mpr h10) h7'
    linarith
  have h9 : (a + b) ^ 2 = b * (a + 3 * b) := by
    have h12 : (b * (a + 3 * b)) ^ (1 / 2 : ℝ) = Real.sqrt (b * (a + 3 * b)) := by
      rw [Real.sqrt_eq_rpow]
    rw [h12] at h8
    have h13 : (Real.sqrt (b * (a + 3 * b))) ^ 2 = b * (a + 3 * b) := Real.sq_sqrt (by positivity)
    have h14 : (a + b) ^ 2 = b * (a + 3 * b) := by
      calc
        (a + b) ^ 2 = ( (a + b) ) ^ 2 := by ring
        _ = (Real.sqrt (b * (a + 3 * b)) ) ^ 2 := by rw [h8]
        _ = b * (a + 3 * b) := h13
    nlinarith
  have h10 : a ^ 2 + a * b - 2 * b ^ 2 = 0 := by
    nlinarith [h9]
  have h11 : a = b := by
    have h12 : a ^ 2 + a * b - 2 * b ^ 2 = 0 := h10
    have h13 : a ^ 2 + a * b - 2 * b ^ 2 = (a - b) * (a + 2 * b) := by
      ring
    rw [h13] at h12
    cases' (mul_eq_zero.1 h12) with h14 h15
    · -- The case `a - b = 0` implies `a = b`
      linarith
    · -- Show that the case `a + 2b = 0` is impossible
      nlinarith
  have h12 : a / b = 1 := by
    have h14 : a = b := h11
    rw [h14]
    field_simp
  rw [h12]
  all_goals
    norm_num
    all_goals nlinarith [Real.pi_pos]