import Mathlib

theorem algebra_208655 (a b c d : ℝ) (ha : 0 < a) (hd : 0 < d) (hdc : d < c) (hcb : c < b)
    (hba : b < a) (x y z : ℝ) (hx : x = Real.sqrt (a * b) + Real.sqrt (c * d))
    (hy : y = Real.sqrt (a * c) + Real.sqrt (b * d)) (hz : z = Real.sqrt (a * d) + Real.sqrt (b * c)) :
    x > y ∧ y > z := by
  have h1 : 0 < b := by linarith
  have h2 : 0 < c := by linarith
  -- Split into two goals: x > y and y > z
  constructor
  · -- Prove x > y
    rw [hx, hy]
    -- Show that $\sqrt{a b} + \sqrt{c d} > \sqrt{a c} + \sqrt{b d}$
    have h4 : 0 < a * b := by nlinarith
    have h5 : 0 < c * d := by nlinarith
    have h6 : 0 < a * c := by nlinarith
    have h7 : 0 < b * d := by nlinarith
    have h8 : Real.sqrt (a * b) + Real.sqrt (c * d) > Real.sqrt (a * c) + Real.sqrt (b * d) := by
      have h9 : (Real.sqrt (a * b) + Real.sqrt (c * d)) ^ 2 > (Real.sqrt (a * c) + Real.sqrt (b * d)) ^ 2 := by
        have h10 : (Real.sqrt (a * b) + Real.sqrt (c * d)) ^ 2 = (Real.sqrt (a * b)) ^ 2 + (Real.sqrt (c * d)) ^ 2 + 2 * (Real.sqrt (a * b) * Real.sqrt (c * d)) := by ring
        have h11 : (Real.sqrt (a * c) + Real.sqrt (b * d)) ^ 2 = (Real.sqrt (a * c)) ^ 2 + (Real.sqrt (b * d)) ^ 2 + 2 * (Real.sqrt (a * c) * Real.sqrt (b * d)) := by ring
        rw [h10, h11]
        have h12 : (Real.sqrt (a * b)) ^ 2 = a * b := Real.sq_sqrt (by nlinarith)
        have h13 : (Real.sqrt (c * d)) ^ 2 = c * d := Real.sq_sqrt (by nlinarith)
        have h14 : (Real.sqrt (a * c)) ^ 2 = a * c := Real.sq_sqrt (by nlinarith)
        have h15 : (Real.sqrt (b * d)) ^ 2 = b * d := Real.sq_sqrt (by nlinarith)
        have h16 : Real.sqrt (a * b) * Real.sqrt (c * d) = Real.sqrt ((a * b) * (c * d)) := by
          rw [← Real.sqrt_mul (by nlinarith)]
          all_goals norm_num
        have h17 : Real.sqrt (a * c) * Real.sqrt (b * d) = Real.sqrt ((a * c) * (b * d)) := by
          rw [← Real.sqrt_mul (by nlinarith)]
          all_goals norm_num
        rw [h12, h13, h14, h15, h16, h17]
        have h18 : (a * b * c * d) = (a * b * c * d) := by ring
        nlinarith [Real.sqrt_nonneg ((a * b) * (c * d)), Real.sqrt_nonneg ((a * c) * (b * d)), Real.sq_sqrt (show (0 : ℝ) ≤ (a * b * c * d) by positivity), mul_pos (sub_pos.mpr (show a > d by linarith)) (sub_pos.mpr (show b > c by linarith)), Real.sqrt_nonneg (a * b), Real.sqrt_nonneg (c * d), Real.sqrt_nonneg (a * c), Real.sqrt_nonneg (b * d)]
      have h10 : Real.sqrt (a * b) + Real.sqrt (c * d) > 0 := by
        positivity
      have h11 : Real.sqrt (a * c) + Real.sqrt (b * d) > 0 := by
        positivity
      nlinarith [Real.sqrt_nonneg (a * b), Real.sqrt_nonneg (c * d), Real.sqrt_nonneg (a * c), Real.sqrt_nonneg (b * d), h9]
    linarith
  · -- Prove y > z
    rw [hy, hz]
    -- Show that $\sqrt{a c} + \sqrt{b d} > \sqrt{a d} + \sqrt{b c}$
    have h4 : 0 < a * c := by nlinarith
    have h5 : 0 < b * d := by nlinarith
    have h6 : 0 < a * d := by nlinarith
    have h7 : 0 < b * c := by nlinarith
    have h8 : Real.sqrt (a * c) + Real.sqrt (b * d) > Real.sqrt (a * d) + Real.sqrt (b * c) := by
      have h9 : (Real.sqrt (a * c) + Real.sqrt (b * d)) ^ 2 > (Real.sqrt (a * d) + Real.sqrt (b * c)) ^ 2 := by
        have h10 : (Real.sqrt (a * c) + Real.sqrt (b * d)) ^ 2 = (Real.sqrt (a * c)) ^ 2 + (Real.sqrt (b * d)) ^ 2 + 2 * (Real.sqrt (a * c) * Real.sqrt (b * d)) := by ring
        have h11 : (Real.sqrt (a * d) + Real.sqrt (b * c)) ^ 2 = (Real.sqrt (a * d)) ^ 2 + (Real.sqrt (b * c)) ^ 2 + 2 * (Real.sqrt (a * d) * Real.sqrt (b * c)) := by ring
        rw [h10, h11]
        have h12 : (Real.sqrt (a * c)) ^ 2 = a * c := Real.sq_sqrt (by nlinarith)
        have h13 : (Real.sqrt (b * d)) ^ 2 = b * d := Real.sq_sqrt (by nlinarith)
        have h14 : (Real.sqrt (a * d)) ^ 2 = a * d := Real.sq_sqrt (by nlinarith)
        have h15 : (Real.sqrt (b * c)) ^ 2 = b * c := Real.sq_sqrt (by nlinarith)
        have h16 : Real.sqrt (a * c) * Real.sqrt (b * d) = Real.sqrt ((a * c) * (b * d)) := by
          rw [← Real.sqrt_mul (by nlinarith)]
          all_goals norm_num
        have h17 : Real.sqrt (a * d) * Real.sqrt (b * c) = Real.sqrt ((a * d) * (b * c)) := by
          rw [← Real.sqrt_mul (by nlinarith)]
          all_goals norm_num
        rw [h12, h13, h14, h15, h16, h17]
        have h18 : (a * c * b * d) = (a * c * b * d) := by ring
        nlinarith [Real.sqrt_nonneg ((a * c) * (b * d)), Real.sqrt_nonneg ((a * d) * (b * c)), Real.sq_sqrt (show (0 : ℝ) ≤ (a * c * b * d) by positivity), mul_pos (sub_pos.mpr (show a > b by linarith)) (sub_pos.mpr (show c > d by linarith)), Real.sqrt_nonneg (a * c), Real.sqrt_nonneg (b * d), Real.sqrt_nonneg (a * d), Real.sqrt_nonneg (b * c)]
      have h10 : Real.sqrt (a * c) + Real.sqrt (b * d) > 0 := by
        positivity
      have h11 : Real.sqrt (a * d) + Real.sqrt (b * c) > 0 := by
        positivity
      nlinarith [Real.sqrt_nonneg (a * c), Real.sqrt_nonneg (b * d), Real.sqrt_nonneg (a * d), Real.sqrt_nonneg (b * c), h9]
    linarith