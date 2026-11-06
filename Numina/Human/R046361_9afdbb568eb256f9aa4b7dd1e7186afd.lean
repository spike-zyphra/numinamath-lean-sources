import Mathlib
open Real

/- 3. Given $x, y$ are in the interval $(-2,2)$, and $x y=-1$, then the minimum value of the function $u=\frac{4}{4-x^{2}}+\frac{9}{9-y^{2}}$ is-/
theorem algebra_215271 :
    IsLeast {u : ℝ | ∃ x y : ℝ, x ∈ Set.Ioo (-2) 2 ∧ y ∈ Set.Ioo (-2) 2 ∧ x * y = -1 ∧ u = 4 / (4 - x ^ 2) + 9 / (9 - y ^ 2)} (12 / 5) := by
  -- Simplify the goal into two parts.
  simp [IsLeast, lowerBounds]
  constructor
  . -- Show that the minimum value 12 / 5 could be attained.
    -- Take x = √2 / √3, y = -√3 / √2.
    use (Real.sqrt (2 / 3)), ⟨?_, ?_⟩, -Real.sqrt (3 / 2), ⟨?_, ?_⟩, ?_, ?_
    . linarith only [show Real.sqrt (2 / 3) > 0 by positivity]
    . rw [Real.sqrt_lt]
      <;> norm_num
    . rw [neg_lt, neg_neg, Real.sqrt_lt]
      <;> norm_num
    . linarith only [show Real.sqrt (3 / 2) > 0 by positivity]
    . field_simp
      ac_rfl
    . field_simp
      norm_num
  . -- Verify that 12 / 5 is minimum.
    intro u x hx hx' y hy hy' hxy hu
    rw [hu, <-ge_iff_le]
    calc
      _ = (72 - 4 * y ^ 2 - 9 * x ^ 2) / ((4 - x ^ 2) * (9 - y ^ 2)) := by
        -- Commonize the denominator.
        field_simp [show 4 - x ^ 2 ≠ 0 by nlinarith, show 9 - y ^ 2 ≠ 0 by nlinarith]
        ring
      _ = 1 + 35 / (37 - (9 * x ^ 2 + 4 * y ^ 2)) := by
        -- Show that x²y² = 1, so (4 - x²)(9 - y²) = 37 - (9x² + 4y²), and simplify the denominator.
        have : (4 - x ^ 2) * (9 - y ^ 2) = 37 - (9 * x ^ 2 + 4 * y ^ 2) := by
          ring_nf
          rw [show x ^ 2 * y ^ 2 = 1 by nlinarith]
          ring
        rw [one_add_div, this]
        congr
        ring
        -- Verify that the denominator is non-zero.
        rw [<-this]
        field_simp [show 4 - x ^ 2 ≠ 0 by nlinarith, show 9 - y ^ 2 ≠ 0 by nlinarith]
      _ ≥ 1 + 35 / (37 - 12) := by
        rw [ge_iff_le, add_le_add_iff_left, div_le_div_iff_of_pos_left (by norm_num) (by norm_num), sub_le_sub_iff_left]
        . -- Show that 12 ≤ 9x² + 4y². We use the fact that (3x + 2y)² ≥ 0 and xy = -1.
          linarith only [sq_nonneg (3 * x + 2 * y), hxy]
        . -- Show that 9x² + 4y² < 37. This is basically (4 - x²)(9 - y²) > 0.
          nlinarith [show 4 - x ^ 2 > 0 by nlinarith, show 9 - y ^ 2 > 0 by nlinarith]
      _ = 12 / 5 := by norm_num