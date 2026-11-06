import Mathlib

theorem algebra_189447 {a b N : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a ≠ 1) (h' : b ≠ 1)
    (h'' : N > 0) :
    Real.logb b N = Real.logb a N / Real.logb a b := by
  have h1 : Real.logb b N = Real.log N / Real.log b := by
    rw [Real.logb]
  have h2 : Real.logb a N = Real.log N / Real.log a := by
    rw [Real.logb]
  have h3 : Real.logb a b = Real.log b / Real.log a := by
    rw [Real.logb]
  rw [h1, h2, h3]
  have h4 : Real.log a ≠ 0 := by
    by_contra h4
    -- When Real.log a = 0, a must be 1.
    have h5 : a = 1 := by
      have h6 : Real.log a = 0 := by simpa using h4
      -- We know that $\log a = 0$ means $a = 1$.
      have h7 : a = (Real.exp (Real.log a)) := by
        rw [Real.exp_log]
        all_goals linarith -- ensure a > 0 from ha
      rw [h6] at h7
      -- We use norm_num to compute exp 0 = 1.
      rw [show Real.exp (0 : ℝ) = 1 by norm_num] at h7
      linarith -- now h7 is a = 1
    -- This contradicts with the hypothesis h: a ≠ 1
    tauto -- use the contradiction (a = 1 ∧ a ≠ 1) to close the goal
  field_simp [h4]
  <;> ring_nf <;> field_simp [h4] <;> ring