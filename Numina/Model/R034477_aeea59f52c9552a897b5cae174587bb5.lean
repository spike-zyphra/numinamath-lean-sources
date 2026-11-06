import Mathlib

theorem algebra_9150 : IsLeast {z : ℝ | ∃ x y, z = x + y ∧ 0 < x ∧ 0 < y
∧ x * y - x - 2 * y = 0} (3 + 2 * (Real.sqrt 2)):= by
  constructor
  · -- Show 3 + 2√2 is achievable, using x = 2 + √2 and y = 1 + √2.
    use 2 + Real.sqrt 2
    use 1 + Real.sqrt 2
    constructor
    · -- Show that (2 + √2) + (1 + √2) = 3 + 2√2
      ring
    constructor
    · -- Show that 0 < 2 + √2
      have h1 : 0 < (2 + Real.sqrt 2 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      linarith
    constructor
    · -- Show that 0 < 1 + √2
      have h2 : 0 < (1 + Real.sqrt 2 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      linarith
    · -- Show that (2 + √2)(1 + √2) - (2 + √2) - 2(1 + √2) = 0
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), mul_pos (show (0 : ℝ) < 2 by norm_num) (show (0 : ℝ) < 2 by norm_num)]
  · -- Show that 3 + 2√2 is minimal
    intro z hz
    rcases hz with ⟨x, y, hz, hx, hy, heq⟩
    have h1 : (x - 2) * (y - 1) = 2 := by 
      linarith 
    by_cases h2x : x - 2 > 0 
    · -- Assume x - 2 > 0
      have h2y : y - 1 > 0 := by 
        nlinarith 
      nlinarith [sq_nonneg (x - 2 - Real.sqrt 2), sq_nonneg (y - 1 - Real.sqrt 2), 
          mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          sq_nonneg (x - 2 - (y - 1)), Real.sqrt_nonneg 2
            ]
    by_cases h2y : y - 1 > 0 
    · -- Assume y - 1 > 0 
      have h4x : x - 2 > 0 := by 
        nlinarith 
      nlinarith [sq_nonneg (x - 2 - Real.sqrt 2), sq_nonneg (y - 1 - Real.sqrt 2), 
          mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          sq_nonneg (x - 2 - (y - 1)), Real.sqrt_nonneg 2
            ]
    · -- Assume not h2x and not h2y 
      push_neg at h2x 
      push_neg at h2y 
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 1), sq_nonneg (x - 2 - Real.sqrt 2), sq_nonneg (y - 1 + Real.sqrt 2), 
          mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          sq_nonneg (x - 2 - (y - 1)), Real.sqrt_nonneg 2
            ]