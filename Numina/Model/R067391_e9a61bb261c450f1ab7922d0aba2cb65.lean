import Mathlib

theorem algebra_290135 :
    IsLeast {t : ℝ | ∃ x y, t = x^4 - 2 * x * y + y^4} (-1 / 2) := by
  constructor
  · -- Show that -1/2 is in the set.
    use Real.sqrt 2 / 2, Real.sqrt 2 / 2
    have h1 : 0 ≤ (Real.sqrt 2 : ℝ) := Real.sqrt_nonneg 2
    have h2 : (Real.sqrt 2 / 2 : ℝ) ^ 4 = 1 / 4 := by
      calc
        (Real.sqrt 2 / 2 : ℝ) ^ 4 = (Real.sqrt 2 ^ 4) / (2 ^ 4 : ℝ) := by ring
        _ = (4 : ℝ) / (16 : ℝ) := by
          have h3 : Real.sqrt 2 ^ 4 = 4 := by
            calc
              Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 := by ring
              _ = (2 : ℝ) ^ 2 := by rw [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
              _ = (4 : ℝ) := by norm_num
          rw [h3]
          all_goals norm_num
        _ = (1 / 4 : ℝ) := by norm_num
    have h3 : -2 * (Real.sqrt 2 / 2 : ℝ) * (Real.sqrt 2 / 2 : ℝ) = -1 := by
      calc
        -2 * (Real.sqrt 2 / 2 : ℝ) * (Real.sqrt 2 / 2 : ℝ)
          = -2 * ((Real.sqrt 2) ^ 2 / 4 : ℝ) := by ring
        _ = -2 * (2 / 4 : ℝ) := by rw [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
        _ = -1 := by norm_num
    linarith [h2, h3]
  · -- Show that -1/2 is the smallest
    intro t ht
    rcases ht with ⟨x, y, h_eq⟩
    have h1 : x^4 - 2 * x * y + y^4 ≥ -1 / 2 := by
      nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x^2 + y^2 - 1), sq_nonneg (x - y), sq_nonneg (x * y - 1 / 2), sq_nonneg (x - Real.sqrt 2 / 2), sq_nonneg (y - Real.sqrt 2 / 2), sq_nonneg (x + Real.sqrt 2 / 2), sq_nonneg (y + Real.sqrt 2 / 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    linarith [h_eq, h1]