import Mathlib

theorem algebra_265450 (x : ℝ) :
    x^3 + (3 * Real.sqrt 2 - 2) * x^2 - (1 + Real.sqrt 2) * x - 14 * (Real.sqrt 2 - 1) = 0 ↔
    x = -2 ∨ x = 3 - Real.sqrt 2 ∨ x = 1 - 2 * Real.sqrt 2 := by
  constructor
  · -- Forward direction: if \( x \) is a root of the equation, prove \( x = -2 \) or \( x = 3-\sqrt{2} \) or \( x = 1-2\sqrt{2} \)
    intro h
    have h1 : x^3 + (3 * Real.sqrt 2 - 2) * x^2 - (1 + Real.sqrt 2) * x - 14 * (Real.sqrt 2 - 1) = 
          (x + 2) * (x - (3 - Real.sqrt 2)) * (x - (1 - 2 * Real.sqrt 2)) := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), 
          mul_self_nonneg (x + 2), mul_self_nonneg (x - (3 - Real.sqrt 2)), 
          mul_self_nonneg (x - (1 - 2 * Real.sqrt 2)), 
          Real.sqrt_nonneg 2]
    rw [h1] at h
    cases' (mul_eq_zero.1 h) with h2 h3
    · cases' (mul_eq_zero.1 h2) with h4 h5
      · -- Case \( x + 2 = 0 \)
        left
        linarith
      · -- Case \( x - (3 - \sqrt{2}) = 0 \)
        right
        left
        linarith
    · -- Case \( x - (1 - 2\sqrt{2}) = 0 \)
      right
      right
      linarith
  · -- Backward direction: if \( x \) is one of the roots \( -2, 3-\sqrt{2}, 1-2\sqrt{2} \), prove it's a root of the equation
    rintro (h | h | h)
    · -- Case \( x = -2 \)
      rw [h]
      nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), 
          mul_self_nonneg (Real.sqrt 2)]
    · -- Case \( x = 3 - \sqrt{2} \)
      rw [h]
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), 
          mul_self_nonneg (3 - Real.sqrt 2), 
          mul_self_nonneg (Real.sqrt 2)]
    · -- Case \( x = 1 - 2\sqrt{2} \)
      rw [h]
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), 
          mul_self_nonneg (1 - 2 * Real.sqrt 2), 
          mul_self_nonneg (Real.sqrt 2)]