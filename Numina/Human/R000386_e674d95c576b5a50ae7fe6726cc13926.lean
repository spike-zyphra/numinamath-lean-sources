import Mathlib
open Real Set

/- The range of the inclination angle of the line $y=x\cdot\cos \theta+4$ is ______________ ($\theta$ is any real number). -/
theorem algebra_9351 :
  {α ∈ Ico 0 (π / 2) ∪ Ioo (π / 2) π | tan α ∈ range cos} = Icc 0 (π / 4) ∪ Ico (3 * π / 4) π := by
  -- Note on formulation of the problem:
  -- The range of the inclination angle of the line $y=x·cos θ+4$ is the set of angles $α$ such that $tan α = cos θ$ for some real number $θ$.
  -- α ∈ [0, π) \ {π/2}

  -- Split the problem into two goals (The range of cos is automatically simplified to [-1, 1])
  -- 1. If (0 ≤ α ∧ α < π / 2 ∨ π / 2 < α ∧ α < π) ∧ -1 ≤ tan α ∧ tan α ≤ 1, then 0 ≤ α ∧ α ≤ π / 4 ∨ 3 * π / 4 ≤ α ∧ α < π
  -- 2. If 0 ≤ α ∧ α ≤ π / 4 ∨ 3 * π / 4 ≤ α ∧ α < π, then (0 ≤ α ∧ α < π / 2 ∨ π / 2 < α ∧ α < π) ∧ -1 ≤ tan α ∧ tan α ≤ 1
  ext α
  simp
  constructor <;> intro h

  . -- First goal, break down the cases of the hypothesis
    obtain ⟨⟨h1, h2⟩ | ⟨h1, h2⟩, h3, h4⟩ := h

    . -- Case 1: 0 ≤ α < π / 2
      -- -1 = tan(-π/4) ≤ tan α ≤ tan(π/4) = 1
      -- Use the strict monotonicity of tan on (-π/2, π/2), and we get 0 ≤ α ≤ π / 4
      left
      clear h3
      rw [(by simp : 1 = tan (π / 4))] at h4
      rw [StrictMonoOn.le_iff_le Real.strictMonoOn_tan] at h4
      all_goals
        constructor <;> linarith

    . -- Case 2: π / 2 < α < π
      -- -1 = tan(-π/4) ≤ tan (π - α) = -tan α ≤ tan(π/4) = 1
      -- Use the strict monotonicity of tan on (-π/2, π/2), and we get 3 * π / 4 ≤ α < π
      right
      clear h4
      replace h3 : tan (π - α) ≤ tan (π / 4) := by linarith [tan_pi_sub α, (by simp : tan (π / 4) = 1)]
      rw [StrictMonoOn.le_iff_le Real.strictMonoOn_tan] at h3
      all_goals
        constructor <;> linarith

  . -- Second goal, break down the cases of the hypothesis
    obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := h

    . -- Case 1: 0 ≤ α ≤ π / 4
      -- Choose the correct subgoal
      refine ⟨Or.inl ⟨by linarith, by linarith [pi_pos]⟩, ?_, ?_⟩
      -- We need to prove -1 ≤ tan α ≤ 1
      -- Use the strict monotonicity of tan on (-π/2, π/2)
      . rw [(by simp : -1 = tan (- (π / 4))), StrictMonoOn.le_iff_le Real.strictMonoOn_tan]
        all_goals
          (try constructor) <;> linarith [pi_pos]
      . rw [(by simp : 1 = tan (π / 4)), StrictMonoOn.le_iff_le Real.strictMonoOn_tan]
        all_goals
          (try constructor) <;> linarith [pi_pos]

    . -- Case 2: 3 * π / 4 ≤ α < π
      -- Choose the correct subgoal
      refine ⟨Or.inr ⟨by linarith, by linarith [pi_pos]⟩, ?_, ?_⟩
      -- We need to prove -1 ≤ tan α ≤ 1
      -- Which is equivalent to -1 ≤ tan (π - α) ≤ 1
      -- Use the strict monotonicity of tan on (-π/2, π/2)
      . suffices _ : tan (π - α) ≤ tan (π / 4) by linarith [tan_pi_sub α, (by simp : tan (π / 4) = 1)]
        rw [StrictMonoOn.le_iff_le Real.strictMonoOn_tan]
        all_goals
          (try constructor) <;> linarith [pi_pos]
      . suffices _ : tan (- (π / 4)) ≤ tan (π - α) by linarith [tan_pi_sub α, (by simp : -1 = tan (- (π / 4)))]
        rw [StrictMonoOn.le_iff_le Real.strictMonoOn_tan]
        all_goals
          (try constructor) <;> linarith [pi_pos]
