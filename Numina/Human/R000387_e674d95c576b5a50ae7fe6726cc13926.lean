import Mathlib
open Real Set

theorem algebra_9351 :
  {α ∈ Ico 0 (π / 2) ∪ Ioo (π / 2) π | tan α ∈ range cos} = Icc 0 (π / 4) ∪ Ico (3 * π / 4) π := by
  ext α
  simp
  constructor <;> intro h

  . obtain ⟨⟨h1, h2⟩ | ⟨h1, h2⟩, h3, h4⟩ := h
    . left
      clear h3
      rw [(by simp : 1 = tan (π / 4))] at h4
      rw [StrictMonoOn.le_iff_le Real.strictMonoOn_tan] at h4
      all_goals
        constructor <;> linarith

    . right
      replace h3 : tan (π - α) ≤ tan (π / 4) := by linarith [tan_pi_sub α, (by simp : tan (π / 4) = 1)]
      rw [StrictMonoOn.le_iff_le Real.strictMonoOn_tan] at h3
      all_goals
        constructor <;> linarith

  . obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := h

    . refine ⟨Or.inl ⟨by linarith, by linarith [pi_pos]⟩, ?_, ?_⟩
      . rw [(by simp : -1 = tan (- (π / 4))), StrictMonoOn.le_iff_le Real.strictMonoOn_tan]
        all_goals
          (try constructor) <;> linarith [pi_pos]
      . rw [(by simp : 1 = tan (π / 4)), StrictMonoOn.le_iff_le Real.strictMonoOn_tan]
        all_goals
          (try constructor) <;> linarith [pi_pos]

    . refine ⟨Or.inr ⟨by linarith, by linarith [pi_pos]⟩, ?_, ?_⟩
      . suffices _ : tan (π - α) ≤ tan (π / 4) by linarith [tan_pi_sub α, (by simp : tan (π / 4) = 1)]
        rw [StrictMonoOn.le_iff_le Real.strictMonoOn_tan]
        all_goals
          (try constructor) <;> linarith [pi_pos]
      . suffices _ : tan (- (π / 4)) ≤ tan (π - α) by linarith [tan_pi_sub α, (by simp : -1 = tan (- (π / 4)))]
        rw [StrictMonoOn.le_iff_le Real.strictMonoOn_tan]
        all_goals
          (try constructor) <;> linarith [pi_pos]
