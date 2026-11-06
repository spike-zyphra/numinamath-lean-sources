import Mathlib

theorem algebra_21422 :
    IsLeast {z : ℝ | ∃ x y, z = x^6 + y^6 - 54 * x * y} (-108) := by

  constructor
  · -- Show that -108 is in the set.
    use Real.sqrt 3, Real.sqrt 3
    have h1 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by linarith)
    have h2 : (Real.sqrt 3 : ℝ) ^ 6 = 27 := by
      calc
        (Real.sqrt 3 : ℝ) ^ 6 = ((Real.sqrt 3 : ℝ) ^ 2) ^ 3 := by ring
        _ = 3 ^ 3 := by rw [h1]
        _ = 27 := by norm_num
    linarith [h2]
  · -- Show that -108 is the least
    intro z h
    rcases h with ⟨x, y, hz⟩
    nlinarith [sq_nonneg (x^3 - y^3), sq_nonneg (x^3 + y^3), sq_nonneg (x^2 - 3), sq_nonneg (y^2 - 3), 
          sq_nonneg (x - Real.sqrt 3), sq_nonneg (x + Real.sqrt 3), sq_nonneg (y - Real.sqrt 3), sq_nonneg (y + Real.sqrt 3),
          Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]