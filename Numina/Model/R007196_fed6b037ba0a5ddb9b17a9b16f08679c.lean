import Mathlib

theorem algebra_14879 :
  IsLeast {y : ℝ | ∃ x, y = (12 - x) * (10 - x) * (12 + x) * (10 + x)} (-484) := by
  constructor
  · -- Show that -484 is in the set.
    -- Taking $x = \pm\sqrt{122}$, which gives us $(12 - x)(10 - x)(12 + x)(10 + x) = -484$.
    use Real.sqrt 122
    nlinarith [sq_nonneg (Real.sqrt 122 - 10), sq_nonneg (Real.sqrt 122 - 12), sq_nonneg (Real.sqrt 122 ^ 2 - 122), Real.sq_sqrt (show (0 : ℝ) ≤ (122 : ℝ) by norm_num)]
  
  · -- Show that -484 is a lower bound.
    intro y
    rintro ⟨x, hx⟩
    have h : (12 - x) * (10 - x) * (12 + x) * (10 + x) = (x ^ 4 - 244 * x ^ 2 + 14400) := by
      ring
    rw [h] at hx
    nlinarith [sq_nonneg ((x ^ 2) - 122), sq_nonneg (x ^ 2 - 122)]