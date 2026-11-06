import Mathlib
open Real

/- This lemma is useful in the main result since it appears in the denominator
-/
lemma lemma_1 : sin (π/18) ≠ 0 := by
  · rw [sin_ne_zero_iff]
    intro n
    ring_nf
    rw [mul_comm]
    simp only [one_div, ne_eq, mul_eq_mul_left_iff, not_or]
    push_neg
    constructor
    . by_contra! hc₀
      have hc₁: 18 * (n : ℝ) = 1 := by
        rw [mul_comm]
        exact (mul_eq_one_iff_eq_inv₀ (by norm_num)).mpr hc₀
      norm_cast at hc₁
      have g₀: 0 < n := by linarith
      linarith
    . exact pi_ne_zero

/- Example 3 Find the value of $\cot 10^{\circ}-4 \cos 10^{\circ}$. -/
theorem algebra_178443 : cot (π/18) - 4 * cos (π/18) = √3 := by calc
  -- rearrange using double angle formulae and conclude
    _ = (cos (π/18) - 4 * cos (π/18) * sin (π/18)) / sin (π/18) := by rw [sub_div, cot_eq_cos_div_sin, mul_div_cancel_right₀ _ lemma_1]
    _ = (sin (π/2 - π/18) - 2 * sin (2 * (π/18))) / sin (π/18) := by congr 1; rw [sin_two_mul, sin_pi_div_two_sub]; ring
    _ = (sin (4/9 * π) - 2 * sin (4/9 * π - π/3)) / sin (π/18) := by congr <;> ring
    _ = (√3 * cos (4/9 * π)) / sin (π/2 - 4/9 * π) := by congr 1; rw [sin_sub, cos_pi_div_three, sin_pi_div_three]; ring; congr 1; ring
    _ = √3 := by rw [←sin_pi_div_two_sub, mul_div_cancel_right₀]; rw [show π/2 - 4/9 * π = π/18 by ring]; exact lemma_1