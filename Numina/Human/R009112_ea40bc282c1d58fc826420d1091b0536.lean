import Mathlib

/- Example 5 Given $a>0, b>0, a+2b=1$, find the minimum value of $t=\frac{1}{a}+\frac{1}{b}$.-/
theorem algebra_597823 :
    IsLeast {t : ℝ | ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + 2 * b = 1 ∧ t = 1 / a + 1 / b} (3 + 2 * Real.sqrt 2) := by
  simp [IsLeast, lowerBounds, -one_div]
  constructor
  . -- First show that 3 + 2√2 is attainable.
    -- Use a = √2 - 1, b = 1 - √2 / 2.
    -- Verify that a, b > 0.
    have h₀ : Real.sqrt 2 - 1 > 0 := by
      simp
      rw [Real.lt_sqrt]
      <;> norm_num
    have h₁ : 2 - Real.sqrt 2 > 0 := by
      simp
      rw [Real.sqrt_lt]
      <;> norm_num
    use Real.sqrt 2 - 1, h₀, 1 - Real.sqrt 2 / 2, ?_, ?_, ?_
    . simp
      rw [div_lt_iff₀]
      . simp_all
      . norm_num
    . field_simp
      norm_num
    . -- Verify that 1 / a + 1 / b = 3 + 2√2.
      field_simp
      ring_nf
      nth_rw 2 [show 3 = 2 + 1 by norm_num]
      rw [pow_add]
      field_simp
      ring
  . -- Show that 3 + 2√2 is the least value of the set.
    intro t a ha b hb h ht
    rw [ht]
    apply le_of_sub_nonneg
    rw [<-ge_iff_le]
    -- Show that b(1 - 2b) > 0, which will be useful to justify the positivity of denominator later.
    have h₀ : b * (1 - 2 * b) > 0 := by
      rw [show 1 - 2 * b = a by linarith]
      positivity
    -- It suffices to show that 1 / a + 1 / b - (3 + 2 √2) ≥ 0.
    calc
      _ = ((6 + 4 * Real.sqrt 2) * b ^ 2 + (-4 - 2 * Real.sqrt 2) * b + 1) / (b * (1 - 2 * b)) := by
        field_simp [show a = 1 - 2 * b by linarith, show 1 - 2 * b ≠ 0 by linarith]
        ring
      _ ≥ 0 := by
        apply div_nonneg
        . -- Use the fact that (b - (1 - Real.sqrt 2 / 2))² ≥ 0, where b = 1 - Real.sqrt 2 / 2 is the equality case.
          nlinarith [sq_nonneg (b - (1 - Real.sqrt 2 / 2)), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
        . exact le_of_lt h₀