import Mathlib

/- Let $a, b, c$ be real numbers greater than or equal to 1 . Prove that  $$ \min \left(\frac{10 a^{2}-5 a+1}{b^{2}-5 b+10}, \frac{10 b^{2}-5 b+1}{c^{2}-5 c+10}, \frac{10 c^{2}-5 c+1}{a^{2}-5 a+10}\right) \leq a b c $$ -/
theorem inequalities_604632 (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    min (min
      ((10 * a ^ 2 - 5 * a + 1) / (b ^ 2 - 5 * b + 10))
      ((10 * b ^ 2 - 5 * b + 1) / (c ^ 2 - 5 * c + 10)))
      ((10 * c ^ 2 - 5 * c + 1) / (a ^ 2 - 5 * a + 10)) ≤ a * b * c := by

  -- prop for some positivity
  --for $x \ge 1$, $x^2 - 5x + 10$ is positive
  have p1 {x : ℝ} (hx : 1 ≤ x) : 0 < (x ^ 2 - 5 * x + 10) := by
    rw [show x ^ 2 - 5 * x + 10 = (x - 5 / 2) ^ 2 + 15 / 4 by ring_nf]
    positivity
  -- for $x \ge 1$, $10x^2 - 5x + 1$ is nonnegative
  have p2 {x : ℝ} (hx : 1 ≤ x) : 0 ≤ (10 * x ^ 2 - 5 * x + 1) / (x ^ 2 - 5 * x + 10) := by
    refine div_nonneg ?_ (le_of_lt (p1 hx))
    nlinarith

  -- Notice that $$ \frac{10 a^{2}-5 a+1}{a^{2}-5 a+10} \leq a^{3} $$ since it rearranges to $(a-1)^{5} \geq 0$.
  -- we need to reuse a variable to generalize for a, b and c.
  have r1 {x : ℝ} (hx : 1 ≤ x) : (10 * x ^ 2 - 5 * x + 1) / (x ^ 2 - 5 * x + 10) ≤ x ^ 3 := by
    have : 0 ≤ (x - 1) ^ 5 := by
      refine pow_nonneg (by linarith only [hx]) 5
    apply (div_le_iff₀ (p1 hx)).mpr
    linarith only [this]

  -- Cyclically multiply to get $$ \prod_{\text{cyc}}\left(\frac{10 a^{2}-5 a+1}{b^{2}-5 b+10}\right) \leq(a b c)^{3} $$
  have r2 : ((10 * a ^ 2 - 5 * a + 1) / (b ^ 2 - 5 * b + 10)) *
            ((10 * b ^ 2 - 5 * b + 1) / (c ^ 2 - 5 * c + 10)) *
            ((10 * c ^ 2 - 5 * c + 1) / (a ^ 2 - 5 * a + 10)) ≤ (a * b * c) ^ 3 := by
    trans ((10 * a ^ 2 - 5 * a + 1) / (a ^ 2 - 5 * a + 10)) *
          ((10 * b ^ 2 - 5 * b + 1) / (b ^ 2 - 5 * b + 10)) *
          ((10 * c ^ 2 - 5 * c + 1) / (c ^ 2 - 5 * c + 10))
    . apply le_of_eq
      ring

    rw [mul_pow, mul_pow]
    refine mul_le_mul (by refine mul_le_mul (r1 ha) (r1 hb) (p2 hb) (by positivity)) (r1 hc) (p2 hc) (by positivity)

  -- and the minimum is at most the geometric mean.
  have r3 {a b c d : ℝ} (hd : 0 < d) :
      a * b * c ≤ d ^ 3 → min (min a b) c ≤ d := by
    intro h
    by_contra! h_contra
    have : d < a ∧ d < b ∧ d < c := by simp_all only [lt_inf_iff, and_self]
    have : d ^ 3 < a * b * c := by
      rw [pow_three, ← mul_assoc]
      gcongr <;> simp_all only
    linarith only [this, h]

  exact r3 (by positivity) r2
