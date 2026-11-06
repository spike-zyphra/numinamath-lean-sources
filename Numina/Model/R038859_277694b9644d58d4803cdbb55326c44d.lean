import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_20476 : IsLeast {x : ℝ | ∃ z : ℂ, x = (z ^ 5).im / z.im ^ 5} (-4) := by
  constructor
  · -- Show -4 is in the set
    use 1 + Complex.I
    have h1 : ((1 + Complex.I) ^ 5 : ℂ).im = -4 := by
      simp [pow_succ, Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re]
      all_goals norm_num
    have h2 : (1 + Complex.I : ℂ).im = 1 := by
      simp
    rw [h1, h2]
    all_goals norm_num
  · -- Show that -4 is the smallest element
    intro x hx
    rcases hx with ⟨z, hx⟩
    have h31 : x ≥ -4 := by
      by_cases h2 : z.im = 0
      · -- If z.im = 0, then x = 0
        have h33 : z.im = 0 := h2
        have h35 : (z ^ 5).im / z.im ^ 5 = 0 := by
          have h40 : (z ^ 5).im = 0 := by
            have h55 : (z ^ 5).im = 5 * z.re ^ 4 * z.im - 10 * z.re ^ 2 * z.im ^ 3 + z.im ^ 5 := by
              simp [pow_succ, Complex.add_im, Complex.mul_im, Complex.ofReal_im, pow_succ, pow_zero, mul_add, mul_assoc]
              ring_nf
            rw [h55]
            rw [show z.im = 0 by exact h33]
            norm_num
          rw [h40, show z.im = (0 : ℝ) by exact h33]
          all_goals norm_num
        rw [show x = (z ^ 5).im / z.im ^ 5 by exact hx] 
        all_goals linarith
      · -- Case z.im ≠ 0
        have h15 : z.im ≠ 0 := h2
        have h21 : x = (5 * (z.re ^ 2 / z.im ^ 2) ^ 2 - 10 * (z.re ^ 2 / z.im ^ 2) + 1 : ℝ) := by
          have h23 : x = (z ^ 5).im / z.im ^ 5 := by
            exact hx
          have h24 : (z ^ 5).im = 5 * z.re ^ 4 * z.im - 10 * z.re ^ 2 * z.im ^ 3 + z.im ^ 5 := by
            simp [pow_succ, Complex.add_im, Complex.mul_im, Complex.ofReal_im, pow_succ, pow_zero, mul_add, mul_assoc]
            ring_nf
          rw [h24] at h23
          have h25 : x = (5 * z.re ^ 4 * z.im - 10 * z.re ^ 2 * z.im ^ 3 + z.im ^ 5) / (z.im ^ 5 : ℝ) := by
            exact h23
          rw [h25]
          have h27 : z.im ≠ 0 := h15
          have h28 : (5 * z.re ^ 4 * z.im - 10 * z.re ^ 2 * z.im ^ 3 + z.im ^ 5 : ℝ) / (z.im ^ 5) =
            5 * (z.re ^ 2 / z.im ^ 2) ^ 2 - 10 * (z.re ^ 2 / z.im ^ 2) + 1 := by
            have h29 : z.im ≠ 0 := h15
            field_simp [h29]
            ring
          exact h28
        have h32 : x ≥ -4 := by
          rw [h21]
          nlinarith [sq_nonneg (z.re ^ 2 / z.im ^ 2 - 1 : ℝ)]
        linarith
    linarith