import Mathlib

theorem algebra_21643 (s : Finset ℝ) (h₀ : s = {2/5, 1/2, 5, 10}) :
    IsGreatest {x | ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ x = a / b} (25) := by
  rw [h₀]
  constructor
  · -- Show 25 is achievable, so it's in the set
    use 10, by norm_num, (2/5 : ℝ), by norm_num
    norm_num
  · -- Show that 25 is greatest
    intro x hx
    rcases hx with ⟨a, ha, b, hb, hneq, heq⟩
    norm_num at ha hb
    rcases ha with (rfl | rfl | rfl | rfl)
    · -- a = 2/5
      rcases hb with (rfl | rfl | rfl | rfl)
      · -- b = 2/5
        exfalso
        norm_num at hneq
      · -- b = 1/2
        norm_num at heq ⊢
        linarith
      · -- b = 5
        norm_num at heq ⊢
        linarith
      · -- b = 10
        norm_num at heq ⊢
        linarith
    · -- a = 1/2
      rcases hb with (rfl | rfl | rfl | rfl)
      · -- b = 2/5
        norm_num at heq ⊢
        linarith
      · -- b = 1/2
        exfalso
        norm_num at hneq
      · -- b = 5
        norm_num at heq ⊢
        linarith
      · -- b = 10
        norm_num at heq ⊢
        linarith
    · -- a = 5
      rcases hb with (rfl | rfl | rfl | rfl)
      · -- b = 2/5
        norm_num at heq ⊢
        linarith
      · -- b = 1/2
        norm_num at heq ⊢
        linarith
      · -- b = 5
        exfalso
        norm_num at hneq
      · -- b = 10
        norm_num at heq ⊢
        linarith
    · -- a = 10
      rcases hb with (rfl | rfl | rfl | rfl)
      · -- b = 2/5
        norm_num at heq ⊢
        linarith
      · -- b = 1/2
        norm_num at heq ⊢
        linarith
      · -- b = 5
        norm_num at heq ⊢
        linarith
      · -- b = 10
        exfalso
        norm_num at hneq