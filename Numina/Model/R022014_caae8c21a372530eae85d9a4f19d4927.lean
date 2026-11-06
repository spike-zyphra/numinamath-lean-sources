import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_217694 :
  IsLeast {x : ℝ | ∃ z : ℂ, z.re ≠ 0 ∧ x = (z^4).re / z.re^4} (-8) := by
  constructor
  · -- Show that -8 is in the set.
    use 1 + Real.sqrt 3 * I
    constructor
    · -- Show that the real part of z = 1 + sqrt(3)*i is non-zero.
      simp [Complex.ext_iff]
    · -- Compute (z^4).re / z.re^4 and show that it equals -8.
      simp [pow_two, pow_succ, Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
      ring_nf
      norm_num [Real.sqrt_mul_self]
  · -- Show that -8 is the least element in the set.
    intro x hx
    rcases hx with ⟨z, hz_re, hx_eq⟩
    have h1 : z.re ≠ 0 := hz_re
    have eq1 : (z ^ 4).re = z.re ^ 4 - 6 * z.re ^ 2 * z.im ^ 2 + z.im ^ 4 := by
      simp [pow_two, pow_succ, Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
      all_goals
      ring_nf
    have h2 : x = (z.re ^ 4 - 6 * z.re ^ 2 * z.im ^ 2 + z.im ^ 4) / z.re ^ 4 := by
      rw [eq1] at hx_eq
      linarith
    have h3 : x ≥ -8 := by
      rw [h2]
      have h4 : (z.re ^ 4 - 6 * z.re ^ 2 * z.im ^ 2 + z.im ^ 4) ≥ -8 * z.re ^ 4 := by
        nlinarith [sq_nonneg (z.re ^ 2 - z.im ^ 2), sq_nonneg (z.re ^ 2 - 3 * z.im ^ 2), sq_nonneg (z.im ^ 2 - 3 * z.re ^ 2), sq_nonneg (z.re ^ 2 + z.im ^ 2), sq_nonneg (z.re * z.im), sq_pos_of_ne_zero (show z.re ≠ 0 by exact h1)]
      have h7 : (z.re ^ 4 - 6 * z.re ^ 2 * z.im ^ 2 + z.im ^ 4) / z.re ^ 4 ≥ -8 := by
        apply (le_div_iff₀ (by
          have : z.re ^ 4 > 0 := by
            have h11 : z.re ≠ 0 := h1
            have h22 : z.re ^ 2 > 0 := by
              exact sq_pos_of_ne_zero h11
            positivity
          linarith
        )).mpr
        nlinarith
      linarith
    linarith