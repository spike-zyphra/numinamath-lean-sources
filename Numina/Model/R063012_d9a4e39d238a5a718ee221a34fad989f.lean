import Mathlib

theorem algebra_296759 {x y z : ℝ} (hx : x = Real.sqrt 2) (hy : y = -Real.sqrt 2) (hz : z = -Real.sqrt 7) :
    x * Real.sqrt (4 - y^2) - y * Real.sqrt (9 - z^2) - z * Real.sqrt (9 - x^2) = 11 := by
  rw [hx, hy, hz]
  have h1' : Real.sqrt (4 - (-Real.sqrt 2) ^ 2) = Real.sqrt 2 := by
    have h2 : (-Real.sqrt 2) ^ 2 = 2 := by
      have h3 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2:ℝ) by norm_num)
      calc
        (-Real.sqrt 2) ^ 2 = (Real.sqrt 2) ^ 2 := by ring
        _ = 2 := h3
    rw [h2]
    all_goals norm_num
  have h4' : Real.sqrt (9 - (-Real.sqrt 7) ^ 2) = Real.sqrt 2 := by
    have h5 : (-Real.sqrt 7) ^ 2 = 7 := by
      have h6 : (Real.sqrt 7) ^ 2 = 7 := Real.sq_sqrt (show 0 ≤ (7:ℝ) by norm_num)
      calc
        (-Real.sqrt 7) ^ 2 = (Real.sqrt 7) ^ 2 := by ring
        _ = 7 := h6
    rw [h5]
    all_goals norm_num
  have h3' : Real.sqrt (9 - (Real.sqrt 2) ^ 2) = Real.sqrt 7 := by
    have h4 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2:ℝ) by norm_num)
    rw [h4]
    all_goals norm_num
  have term1 : Real.sqrt 2 * Real.sqrt (4 - (-Real.sqrt 2) ^ 2) = 2 := by
    rw [h1']
    have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
      calc
        Real.sqrt 2 * Real.sqrt 2 = (Real.sqrt 2) ^ 2 := by ring
        _ = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
    linarith
  have term2 : -(-Real.sqrt 2) * Real.sqrt (9 - (-Real.sqrt 7) ^ 2) = 2 := by
    rw [h4']
    have h23 : -(-Real.sqrt 2) * Real.sqrt 2 = 2 := by
      calc
        -(-Real.sqrt 2) * Real.sqrt 2 = Real.sqrt 2 * Real.sqrt 2 := by ring
        _ = (Real.sqrt 2) ^ 2 := by ring
        _ = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
    linarith
  have term3 : -(-Real.sqrt 7) * Real.sqrt (9 - (Real.sqrt 2) ^ 2) = 7 := by
    rw [h3']
    have h24 : -(-Real.sqrt 7) * Real.sqrt 7 = 7 := by
      calc
        -(-Real.sqrt 7) * Real.sqrt 7 = Real.sqrt 7 * Real.sqrt 7 := by ring
        _ = (Real.sqrt 7) ^ 2 := by ring
        _ = 7 := Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)
    linarith
  linarith [term1, term2, term3]