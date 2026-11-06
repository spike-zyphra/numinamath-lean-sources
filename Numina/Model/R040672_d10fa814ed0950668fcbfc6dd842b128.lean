import Mathlib

open Real Set

theorem inequalities_293739 :
  IsGreatest {a - b + c|(a: ℝ) (b : ℝ) (c : ℝ) (_ : ∀ (x : ℝ), a * cos x + b * cos (2 * x) + c * cos (3 * x) ≥ -1 )} 1
     := by
  constructor
  · -- Show 1 is in the set
    use 1, 0, 0
    simp
    all_goals
      intro x
      have hcos : -1 ≤ cos x ∧ cos x ≤ 1 := by
        constructor
        · linarith [neg_one_le_cos x, cos_le_one x]
        · linarith [neg_one_le_cos x, cos_le_one x]
      linarith [hcos.1, hcos.2]
  · -- Show 1 is greatest
    intro d hd
    rcases hd with ⟨a, b, c, hx, hd⟩
    have h1 := hx Real.pi
    have hcos1 : cos Real.pi = -1 := Real.cos_pi
    have hcos2 : cos (2 * Real.pi) = 1 := Real.cos_two_pi
    have hcos3 : cos (3 * Real.pi) = -1 := by
      have h1 : 3 * Real.pi = Real.pi + 2 * Real.pi := by ring
      rw [h1]
      rw [cos_add, cos_two_pi, sin_two_pi]
      simp
    simp [hcos1, hcos2, hcos3] at h1
    linarith