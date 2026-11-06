import Mathlib

open Real

theorem algebra_78738 {x α : ℝ} (hx : x ≠ 0) (h : x + 1 / x = 2 * Real.cos α) :
    ∀ n : ℕ, x ^ n + 1 / x ^ n = 2 * Real.cos (n * α) := by
  intro n
  have h1 : ∀ (n : ℕ), x ^ n + 1 / x ^ n = 2 * Real.cos (n * α) := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      norm_num
      all_goals simp [Real.cos_zero]
    | succ n =>
      cases n with
      | zero =>
        simpa using h
      | succ n =>
        have eq1 : x ^ (n + 2 : ℕ) + 1 / x ^ (n + 2 : ℕ) = (x + 1 / x) * (x ^ (n + 1 : ℕ) + 1 / x ^ (n + 1 : ℕ)) - (x ^ (n : ℕ) + 1 / x ^ (n : ℕ)) := by
          field_simp [pow_two, pow_succ, hx]
          ring
        rw [eq1]
        have h2 := ih n (by linarith)
        have h3 := ih (n + 1) (by linarith)
        rw [h3, h2, h]
        have h4 : Real.cos ((↑n + 2 : ℝ) * α) = 2 * Real.cos ((↑n + 1 : ℝ) * α) * Real.cos α - Real.cos ((↑n : ℝ) * α) := by
          have h4 : Real.cos ((↑n + 2 : ℝ) * α) + Real.cos ((↑n : ℝ) * α) = 2 * Real.cos ((↑n + 1 : ℝ) * α) * Real.cos α := by
            have h5 : Real.cos ((↑n + 1 : ℝ) * α + α) + Real.cos ((↑n + 1 : ℝ) * α - α) = 2 * Real.cos ((↑n + 1 : ℝ) * α) * Real.cos α := by
              rw [Real.cos_add, Real.cos_sub]
              ring
            have h6 : (↑n + 1 : ℝ) * α + α = (↑n + 2 : ℝ) * α := by ring
            have h7 : (↑n + 1 : ℝ) * α - α = (↑n : ℝ) * α := by
              ring_nf
            rw [h6, h7] at h5
            linarith [h5]
          linarith [h4]
        simp [show (↑(n + 2 : ℕ) : ℝ) = (↑n + 2 : ℝ) by simp] at *
        nlinarith [h4]
  specialize h1 n
  simpa using h1