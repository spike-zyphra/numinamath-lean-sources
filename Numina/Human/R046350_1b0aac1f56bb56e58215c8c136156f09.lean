import Mathlib

theorem algebra_316307 : IsGreatest {x | ∃ t : ℝ, x = 4 * (Real.cos t)^3 - 3 * (Real.cos t)^2 - 6 * Real.cos t + 5} (27 / 4) := by
  constructor
  · -- Let's prove 27/4 is attainable
    use (Real.pi * (2 / 3))
    have h : Real.cos (Real.pi * (2 / 3)) = -1 / 2 := by
      have h1 : Real.cos (Real.pi * (2 / 3)) = -1 / 2 := by
        have h2 : Real.cos (Real.pi * (2 / 3)) = - Real.cos (Real.pi / 3) := by
          rw [show Real.pi * (2 / 3) = Real.pi - Real.pi / 3 by ring]
          rw [Real.cos_pi_sub]
        rw [h2]
        rw [Real.cos_pi_div_three]
        linarith
      exact h1
    rw [h]
    norm_num
  · -- Now, let's prove that 27/4 is an upper bound
    intro x hx
    rcases hx with ⟨t, ht⟩
    rw [ht]
    have ht1 : -1 ≤ Real.cos t := Real.neg_one_le_cos t
    have ht2 : Real.cos t ≤ 1 := Real.cos_le_one t
    nlinarith [sq_nonneg (Real.cos t + 1 / 2), sq_nonneg (Real.cos t - 1)]