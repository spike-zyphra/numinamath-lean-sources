import Mathlib

theorem algebra_20145 (n : ℕ) (h : 0 < n) : √400 = √81 + √n ↔ n = 121 := by
  constructor
  · -- Assume $\sqrt{400} = \sqrt{81} + \sqrt{n}$, prove $n = 121$.
    intro h_eq
    have h1 : √400 = 20 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : √81 = 9 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2] at h_eq
    have h3 : √(n : ℝ) = 11 := by
      linarith
    have h4 : (n : ℝ) = 121 := by
      calc
        (n : ℝ) = (√(n : ℝ)) ^ 2 := by
          rw [Real.sq_sqrt]
          have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
          linarith
        _ = (11 : ℝ) ^ 2 := by
          rw [h3]
        _ = (121 : ℝ) := by
          norm_num
    have h5 : n = 121 := by
      exact_mod_cast h4
    exact h5
  · -- Assume $n = 121$, prove $\sqrt{400} = \sqrt{81} + \sqrt{n}$.
    intro h_eq
    have h1 : √400 = 20 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : √81 = 9 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h3 : √(n : ℝ) = 11 := by
      have h4 : (n : ℝ) = (121 : ℝ) := by
        exact_mod_cast h_eq
      rw [h4]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2, h3]
    all_goals
      norm_num