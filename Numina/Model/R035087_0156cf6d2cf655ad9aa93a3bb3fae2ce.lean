import Mathlib


theorem algebra_21688 :
    IsGreatest {a : ℝ | ∃ b, 5 * a + 2 * b = 0 ∧ a * b = -10} 2 := by
  constructor
  · -- Show 2 is in the set
    use -5
    norm_num
  · -- Show there's no greater element in the set
    intro a ha
    rcases ha with ⟨b, h1, h2⟩
    have hb : b = -5 / 2 * a := by
      nlinarith
    rw [hb] at h2
    nlinarith [sq_nonneg (a - 2), sq_nonneg (a + 2)]