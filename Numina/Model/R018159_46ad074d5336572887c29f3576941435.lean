import Mathlib

theorem algebra_12570 :
    IsGreatest {t : ℝ | ∃ x y z, t = x * y + y * z ∧ x ^ 2 + y ^ 2 + z ^ 2 = 1} (Real.sqrt 2 / 2) := by
  constructor
  · -- Show that sqrt(2)/2 is achievable
    use 1 / 2, Real.sqrt 2 / 2, 1 / 2
    constructor
    · -- Show that it equals sqrt(2)/2
      field_simp
      <;> nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    · -- Show that x^2 + y^2 + z^2 = 1
      have h1 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), h1]
  · -- Show that sqrt(2)/2 is greatest
    intro t ht
    rcases ht with ⟨x, y, z, h_eq, h1⟩
    have h2 : (x * y + y * z) ≤ Real.sqrt 2 / 2 := by
      nlinarith [sq_nonneg (x - z), sq_nonneg (y ^ 2 - (x + z) ^ 2 / 2), sq_nonneg ((x + z) ^ 2 - 2 * y ^ 2), 
        sq_nonneg (x - z), sq_nonneg (x + z - y * Real.sqrt 2), sq_nonneg (x + z + y * Real.sqrt 2), 
        Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
        sq_nonneg (y ^ 2 - 1 / 2), sq_nonneg ((x + z) ^ 2 - 1 / 2)
        ]
    linarith [h_eq, h2]