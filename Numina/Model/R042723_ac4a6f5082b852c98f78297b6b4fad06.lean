import Mathlib 

theorem algebra_91063 : IsGreatest {k | ∃ x y z : ℝ, x^2 + y^2 + z^2 = 1 ∧ k = x*y + y*z -z*x} (1/2)
  ∧ IsLeast {k | ∃ x y z : ℝ, x^2 + y^2 + z^2 = 1 ∧ k = x*y + y*z -z*x} (-1) := by
  constructor 
  · -- Show that 1/2 is the greatest
    constructor 
    · -- Show that 1/2 is in the set.
      use Real.sqrt 6 / (-6), Real.sqrt 6 / 6, Real.sqrt 6 / 3 
      constructor 
      · -- Show x^2 + y^2 + z^2 = 1
        nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
      · -- Show k = x * y + y * z - z * x 
        nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
    · -- Show that 1/2 is indeed the greatest
      intro k hk
      rcases hk with ⟨x, y, z, h_eq, hk_eq⟩
      nlinarith [sq_nonneg (x - y), sq_nonneg (y + z), sq_nonneg (z - x), sq_nonneg (x + y - z), sq_nonneg (x - y + z), sq_nonneg (-x + y + z)]
  · -- Show that -1 is the least 
    constructor 
    · -- Show that -1 is in the set.
      use Real.sqrt 3 / 3, - (Real.sqrt 3 / 3), Real.sqrt 3 / 3
      constructor 
      · -- Show x^2 + y^2 + z^2 = 1 
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      · -- Show k = x * y + y * z - z * x 
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    · -- Show that -1 is indeed the least 
      intro k hk 
      rcases hk with ⟨x, y, z, h_eq, hk_eq⟩
      nlinarith [sq_nonneg (x - y), sq_nonneg (y + z), sq_nonneg (z - x), sq_nonneg (x + y - z), sq_nonneg (x - y + z), sq_nonneg (-x + y + z)]