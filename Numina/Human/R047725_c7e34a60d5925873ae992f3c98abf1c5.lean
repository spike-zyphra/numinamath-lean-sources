import Mathlib

/- The real numbers $x, y, z$ satisfy $0 \leq x \leq y \leq z \leq 4$. If their squares form an arithmetic progression with common difference 2 , determine the minimum possible value of $|x-y|+|y-z|$.-/
theorem algebra_609101 :
    IsLeast {α : ℝ | ∃ x y z : ℝ, 0 ≤ x ∧ x ≤ y ∧ y ≤ z ∧ z ≤ 4 ∧ y ^ 2 = x ^ 2 + 2 ∧ z ^ 2 = y ^ 2 + 2 ∧ α = |x - y| + |y - z|} (4 - 2 * Real.sqrt 3) := by
  -- Break the goal into two parts.
  simp [IsLeast, lowerBounds]
  refine ⟨?_, ?_⟩
  . -- Show that this value (|x - y| + |y - z| = 4 - 2 * Real.sqrt 3) is indeed possible.
    use Real.sqrt 12, by positivity, Real.sqrt 14, by apply Real.sqrt_le_sqrt; norm_num, 4, by rw [Real.sqrt_le_iff]; norm_num, by norm_num
    ring_nf
    repeat rw [Real.sq_sqrt (by norm_num)]
    rw [<-neg_neg (-Real.sqrt 14 + Real.sqrt 12), abs_neg, <-neg_neg (-4 + Real.sqrt 14)]
    nth_rw 2 [abs_neg]
    simp
    rw [abs_of_nonneg (show -Real.sqrt 12 + Real.sqrt 14 ≥ 0 by linarith only [show Real.sqrt 12 ≤ Real.sqrt 14 by apply Real.sqrt_le_sqrt; norm_num])]
    rw [abs_of_nonneg (show -Real.sqrt 14 + 4 ≥ 0 by linarith only [show Real.sqrt 14 ≤ 4 by rw [Real.sqrt_le_iff]; norm_num])]
    have : Real.sqrt 12 = 2 * Real.sqrt 3 := by
      rw [<-sq_eq_sq₀, mul_pow]
      repeat rw [Real.sq_sqrt (by norm_num)]
      all_goals
        norm_num
    rw [this]
    ring_nf
    tauto
  . -- Show that 4 - 2√3 is minimal.
    intro α x h₀ y h₁ z h₂ h₃ h₄ h₅ h₆
    -- Note that |x - y| + |y - z| = z - x.
    rw [<-neg_neg (x - y), <-neg_neg (y - z), abs_neg] at h₆
    nth_rw 2 [abs_neg] at h₆
    simp at h₆
    rw [abs_of_nonneg (show y - x ≥ 0 by linarith only [h₁]), abs_of_nonneg (show z - y ≥ 0 by linarith only [h₂])] at h₆
    simp at h₆
    suffices α ≥ 4 - 2 * Real.sqrt 3 by
      linarith only [this]
    -- Do the estimation step by step.
    calc
      α = (z ^ 2 - y ^ 2 + (y ^ 2 - x ^ 2)) / (z + x) := by
        simp
        rw [sq_sub_sq, mul_div_cancel_left₀]
        exact h₆
        -- It is impossible that z + x = 0, because z² = y² + 2.
        by_contra!
        replace this : z = 0 := by linarith
        rw [this] at h₅
        linarith only [h₅, sq_nonneg y]
      _ = (2 + 2) / (z + x) := by
        congrm (?_ + ?_) / ?_
        . linarith only [h₅]
        . linarith only [h₄]
        . rfl
      _ ≥ 4 / (4 + 2 * Real.sqrt 3) := by
        norm_num
        apply div_le_div₀ (by norm_num) (by rfl)
        -- It is impossible that z + x = 0, because z² = y² + 2.
        by_contra!
        replace this : z = 0 := by linarith
        rw [this] at h₅
        linarith only [h₅, sq_nonneg y]
        -- Show that z + x ≤ 4 + √12.
        apply add_le_add
        . -- Obviously, z ≤ 4.
          exact h₃
        . -- Since z² ≤ 16, x² ≤ 12, x ≤ √12.
          replace h₃ : z ^ 2 ≤ 16 := by nlinarith
          replace h₃ : x ^ 2 ≤ (2 * Real.sqrt 3) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (by norm_num)]
            norm_num
            linarith
          rw [sq_le_sq₀] at h₃
          exact h₃
          exact h₀
          positivity
      _ = 4 - 2 * Real.sqrt 3 := by
        field_simp [show 4 + 2 * Real.sqrt 3 > 0 by positivity]
        ring_nf
        rw [Real.sq_sqrt (by norm_num)]
        norm_num