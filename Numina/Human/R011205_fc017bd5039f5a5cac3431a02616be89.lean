import Mathlib
/- Determine the maximum value attained by

$$
\frac{x^{4}-x^{2}}{x^{6}+2 x^{3}-1}
$$

over real numbers $x>1$. -/
theorem algebra_611433 : IsGreatest {a : ℝ | ∃ x > 1, a = (x ^ 4 - x ^ 2) / (x ^ 6 + 2 * x ^ 3 - 1)} (1 / 6):= by
  constructor
  .
    simp
    -- Use x = 1/2 + √5/2 as the value that achieves 1/6
    use (1 / 2 + √5 / 2)
    constructor
    .
      -- Prove that 1/2 + √5/2 > 1 by showing √5 - 1 > 0
      suffices √5 - 1 > 0 by linarith
      have g1 : (√5 + 1) * (√5 - 1) > 0:= by
        ring_nf
        field_simp
      have g2 : √5 + 1 > 0:= by positivity
      exact (pos_iff_pos_of_mul_pos g1).mp g2
    .
      -- Verify that the function evaluates to 1/6 at x = 1/2 + √5/2
      field_simp
      norm_num
      -- Simplify complex expressions involving √5
      have g1 : (64 * ((1 + √5) ^ 6 * 8 + 2 * (1 + √5) ^ 3 * 64 - 512)) = 393216 + √5 * 196608:= by
        ring_nf
        rw [show √5 ^ 3 = √5 ^ 2 * √5 by ring]
        rw [show √5 ^ 4 = √5 ^ 2 * √5 ^ 2 by ring]
        rw [show √5 ^ 5 = √5 ^ 2 * √5 ^ 2 * √5 by ring]
        rw [show √5 ^ 6 = √5 ^ 2 * √5 ^ 2 * √5 ^ 2 by ring]
        field_simp
        ring_nf
      rw [g1]
      field_simp
      ring_nf
      rw [show √5 ^ 3 = √5 ^ 2 * √5 by ring]
      rw [show √5 ^ 4 = √5 ^ 2 * √5 ^ 2 by ring]
      field_simp
      ring_nf
  .
    -- Prove that 1/6 is an upper bound for all possible values
    simp [upperBounds]
    intro a x hx ha
    subst a
    -- Rewrite the fraction in terms of (x - 1/x)
    have g1 : (x ^ 4 - x ^ 2) / (x ^ 6 + 2 * x ^ 3 - 1) = (x - 1 / x) / (x ^ 3 + 2 - 1 / x ^ 3):= by
      rw [show x - 1 / x = (x ^ 4 - x ^ 2) * (1 / x ^ 3) by field_simp ; linarith]
      rw [show x ^ 3 + 2 - 1 / x ^ 3 = (x ^ 6 + 2 * x ^ 3 - 1) * (1 / x ^ 3) by field_simp ; linarith]
      field_simp
    rw [g1]
    -- Further simplify the denominator
    rw [show x ^ 3 + 2 - 1 / x ^ 3 = (x - 1 / x) * ((x - 1 / x) ^ 2 + 3) + 2 by field_simp ; linarith]
    -- Let t = x - 1/x to simplify the expression
    set t:= x - 1 / x with ht
    -- Prove t > 0 when x > 1
    have ht1 : t > 0:= by
      rw [ht]
      field_simp
      suffices (x - 1) * (x + 1) > 0 by linarith
      replace hx : x - 1 > 0:= by linarith
      have hx1 : x + 1 > 0:= by linarith
      positivity
    clear_value t
    clear ht hx g1 x
    field_simp
    -- Show the denominator is positive
    have g1 : t * (t ^ 2 + 3) + 2 > 0:= by positivity
    -- Prove the inequality using the quadratic form (t - 1)^2 * (t + 2) ≥ 0
    suffices t ≤ (1 / 6) * (t * (t ^ 2 + 3) + 2) by exact (div_le_iff₀ g1).mpr this
    suffices (t - 1) ^ 2 * (t + 2) ≥ 0 by linarith
    positivity
