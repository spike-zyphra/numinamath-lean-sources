import Mathlib

theorem algebra_9095 (a b : ℝ) (h : ∀ x ∈ Set.Icc 0 1, |a * x + b - Real.sqrt (1 - x ^ 2)| ≤ (Real.sqrt 2 - 1) / 2) :
    a = -1 ∧ b = (Real.sqrt 2 + 1) / 2 := by

  have h1 := h 0 (by norm_num)
  have h2 := h 1 (by norm_num)
  have h3 := h (Real.sqrt 2 / 2) (by
    have h1 : 0 ≤ Real.sqrt 2 / 2 := by
      have h2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      linarith
    have h2 : Real.sqrt 2 / 2 ≤ 1 := by
      have h3 : Real.sqrt 2 ≤ 1.5 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 - 1.5)]
      linarith
    exact ⟨h1, h2⟩
  )
  -- Simplify the constraints at x = 0, x = 1, and x = Real.sqrt 2 / 2
  have h1' : - (Real.sqrt 2 - 1) / 2 ≤ b - 1 := by 
    rw [show Real.sqrt (1 - (0 : ℝ) ^ 2) = 1 by norm_num] at h1
    cases abs_le.mp h1 with
    | intro h2 h3 => 
      nlinarith
  -- Simplify the upper bound for b from x = 0.
  have h1'' : b - 1 ≤ (Real.sqrt 2 - 1) / 2 := by
    rw [show Real.sqrt (1 - (0 : ℝ) ^ 2) = 1 by norm_num] at h1
    cases abs_le.mp h1 with
    | intro h2 h3 => 
      nlinarith 
  -- Simplify the lower bound for a + b from x = 1.
  have h2' : - (Real.sqrt 2 - 1) / 2 ≤ a + b := by 
    rw [show Real.sqrt (1 - (1 : ℝ) ^ 2) = 0 by norm_num] at h2
    cases abs_le.mp h2 with
    | intro h3 h4 => 
      nlinarith 
  -- Simplify the upper bound for a + b from x = 1.
  have h2'' : a + b ≤ (Real.sqrt 2 - 1) / 2 := by 
    rw [show Real.sqrt (1 - (1 : ℝ) ^ 2) = 0 by norm_num] at h2
    cases abs_le.mp h2 with
    | intro h3 h4 => 
      nlinarith
  -- Simplify the lower bound for a * (Real.sqrt 2 / 2) + b from x = Real.sqrt 2 / 2
  have h3' : - (Real.sqrt 2 - 1) / 2 ≤ a * (Real.sqrt 2 / 2) + b - Real.sqrt (1 - (Real.sqrt 2 / 2) ^ 2) := by 
    cases abs_le.mp h3 with
    | intro h4 h5 => 
      nlinarith 
  -- Simplify the upper bound for a * (Real.sqrt 2 / 2) + b from x = Real.sqrt 2 / 2
  have h3'' : a * (Real.sqrt 2 / 2) + b - Real.sqrt (1 - (Real.sqrt 2 / 2) ^ 2) ≤ (Real.sqrt 2 - 1) / 2 := by 
    cases abs_le.mp h3 with
    | intro h4 h5 => 
      nlinarith 
  -- Simplify Real.sqrt (1 - (Real.sqrt 2 / 2 ) ^ 2)
  have h3sqrt : Real.sqrt (1 - (Real.sqrt 2 / 2) ^ 2) = Real.sqrt 2 / 2 := by
    have h4 : (1 - (Real.sqrt 2 / 2 : ℝ) ^ 2) = (1 / 2 : ℝ) := by 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [h4]
    have h5 : Real.sqrt (1 / 2 : ℝ) = Real.sqrt 2 / 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      <;> ring_nf <;> norm_num 
    exact h5 
  -- Substitute the simplified value into the bounds
  rw [h3sqrt] at h3' h3''
  -- Now, we solve the system of equations using Lean
  have ha : a = -1 := by 
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (a + 1), sq_nonneg (b - (Real.sqrt 2 + 1) / 2)]
  -- Now that we have a, we solve for b
  have hb : b = (Real.sqrt 2 + 1) / 2 := by 
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (a + 1), sq_nonneg (b - (Real.sqrt 2 + 1) / 2)]
  -- Combining results
  exact ⟨ha, hb⟩