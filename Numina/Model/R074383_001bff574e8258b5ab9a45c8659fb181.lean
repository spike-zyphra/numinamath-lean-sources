import Mathlib

theorem number_theory_7640 (p : ℕ) (hp : p.Prime) :
    ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ p = m^2 + n^2 ∧ p ∣ m^3 + n^3 - 4 ↔ p = 2 ∨ p = 5 := by
  by_cases h : p = 2
  · -- First case: p = 2
    use 1, 1
    simp [h]
    all_goals norm_num [h]

  · -- Second case: p ≠ 2
    by_cases h₂ : p = 5
    · -- Second case: p = 5
      use 1, 2
      simp [h₂]
      all_goals norm_num [h₂]

    · -- Third case: neither p = 2 nor p = 5
      push_neg at h h₂
      use 0, 0
      simp [h, h₂, hp]
      all_goals norm_num
      all_goals try { tauto }
      <;> nlinarith