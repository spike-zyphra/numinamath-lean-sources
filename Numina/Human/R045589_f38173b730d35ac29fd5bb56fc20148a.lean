import Mathlib

open Real Set

/- For real numbers $t > 3,$ find the minimum value of \[\frac{t}{\sqrt{t - 3}}.\] -/
theorem algebra_20603 (f : ℝ → ℝ) (hf : f = fun t => t / sqrt (t - 3)) :
    IsLeast {x | ∃ t, t > 3 ∧ f t = x} (2 * sqrt 3) := by
  constructor
  -- When $t = 6, f(t) = 2\sqrt{3}$
  use 6
  constructor
  linarith
  simp only [hf]
  field_simp
  ring_nf
  rw [sq_sqrt]
  ring
  exact zero_le_three
  -- For any $t > 3, f(t) \geq 2\sqrt{3}$
  intro x hx
  rcases hx with ⟨t, htgt, hteq⟩
  simp [hf] at hteq
  -- Let $a = \sqrt{t - 3}
  let a := sqrt (t - 3)
  -- Then $a ^2 = t - 3$
  have h1 : a ^ 2 = t - 3 := by
    rw [sq_sqrt]
    linarith
  -- So $t = a ^ 2 + 3
  have h2 : t = a ^ 2 + 3 := by
    linarith
  -- Then \[\frac{t}{\sqrt{t - 3}} = \frac{a^2 + 3}{a} = a + \frac{3}{a}.\]
  have agt : 0 < a := by
      dsimp [a]
      refine sqrt_pos_of_pos ?_
      linarith
  have h3 : t / sqrt (t - 3) = a + 3 / a := by
    rw [h2, add_sub_cancel_right, sqrt_sq]
    field_simp [agt]
    rw [pow_two]
    exact sqrt_nonneg (t - 3)
  -- $a + \frac{3}{a} \ge 2 \sqrt{3}$
  rw [← hteq, h3]
  apply le_of_sub_nonneg
  have eq : a + 3 / a - 2 * sqrt 3 = (sqrt a - sqrt (3 / a)) ^ 2 := by
    rw [sub_pow_two, sq_sqrt, sq_sqrt, mul_assoc 2, ← sqrt_mul, mul_div_cancel₀]
    ring
    exact Ne.symm (ne_of_lt agt)
    exact sqrt_nonneg (t - 3)
    apply div_nonneg
    exact zero_le_three
    exact sqrt_nonneg (t - 3)
    exact sqrt_nonneg (t - 3)
  rw [eq]
  exact sq_nonneg (√a - √(3 / a))