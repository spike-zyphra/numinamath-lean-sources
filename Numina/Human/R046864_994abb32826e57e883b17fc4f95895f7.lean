import Mathlib

/- 3. $a$ and $b$ are positive numbers, and $a+b=2$. Prove the inequality

$$
\frac{1}{a^{2}+1}+\frac{1}{b^{2}+1} \geq 1
$$ -/
theorem inequalities_110295 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 2) :
    1 / (a ^ 2 + 1) + 1 / (b ^ 2 + 1) ≥ 1 := by
  -- First, we prove that 1/(a²+1) ≥ (2-a)/2
  have h1 : 1 / (a ^ 2 + 1) ≥ (2 - a) / 2 := by
    -- Establish that a(a-1)² ≥ 0 as a product of non-negative terms
    have h4 : a * (a - 1) ^ 2 ≥ 0 := by
      apply mul_nonneg
      · linarith
      · apply pow_two_nonneg
    -- Prove that 1/(a²+1) - (2-a)/2 ≥ 0 by algebraic manipulation
    have h5 : 1 / (a ^ 2 + 1) - (2 - a) / 2 ≥ 0 := by
      -- Express the difference as a single fraction and show it's non-negative
      have h9 : (2 - (2 - a) * (a ^ 2 + 1)) / (2 * (a ^ 2 + 1)) ≥ 0 := by
        apply div_nonneg
        · linarith
        · nlinarith [sq_nonneg (a - 1)]
      -- Verify that this fraction equals our desired expression
      have h10 : (2 - (2 - a) * (a ^ 2 + 1)) / (2 * (a ^ 2 + 1)) = (1 / (a ^ 2 + 1)) - (2 - a) / 2 := by
        field_simp
        ring
      linarith [h9, h10]
    linarith [h5]
  -- Similarly, prove that 1/(b²+1) ≥ (2-b)/2 using the same approach
  have h2 : 1 / (b ^ 2 + 1) ≥ (2 - b) / 2 := by
    -- Establish that b(b-1)² ≥ 0
    have h5 : b * (b - 1) ^ 2 ≥ 0 := by
      apply mul_nonneg
      · linarith [hb]
      · apply pow_two_nonneg
    -- Prove that 1/(b²+1) - (2-b)/2 ≥ 0
    have h6 : 1 / (b ^ 2 + 1) - (2 - b) / 2 ≥ 0 := by
      -- Express the difference as a single fraction and show it's non-negative
      have h10 : (2 - (2 - b) * (b ^ 2 + 1)) / (2 * (b ^ 2 + 1)) ≥ 0 := by
        apply div_nonneg
        · linarith
        · nlinarith [sq_nonneg (b - 1)]
      -- Verify that this fraction equals our desired expression
      have h11 : (2 - (2 - b) * (b ^ 2 + 1)) / (2 * (b ^ 2 + 1)) = (1 / (b ^ 2 + 1)) - (2 - b) / 2 := by
        field_simp
        ring
      linarith [h10, h11]
    linarith [h6]
  -- Combine the two inequalities to show that the sum is greater than (2-a)/2 + (2-b)/2
  have h3 : 1 / (a ^ 2 + 1) + 1 / (b ^ 2 + 1) ≥ (2 - a) / 2 + (2 - b) / 2 := by
    linarith [h1, h2]
  -- Show that (2-a)/2 + (2-b)/2 = 1 using the constraint a+b=2
  have h4 : (2 - a) / 2 + (2 - b) / 2 = 1 := by
    linarith [h]
  -- Conclude that 1/(a²+1) + 1/(b²+1) ≥ 1
  linarith [h3, h4]
