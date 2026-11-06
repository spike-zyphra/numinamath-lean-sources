import Mathlib

theorem number_theory_236261 (A B : ℕ) (hA : A ≠ 0) (hB : B ≠ 0) (hAB : A^3 = 1008 * B) :
    IsLeast {x | ∃ A B : ℕ, A ≠ 0 ∧ B ≠ 0 ∧ A^3 = 1008 * B ∧ B = x} 588 := by
  constructor
  · -- proving 588 is in the set, witness (84, 588)
    use 84, 588
    all_goals norm_num
  · -- proving no smaller element is in the set
    intro x hx
    rcases hx with ⟨A, B, hA, hB, hAB, hBx⟩
    by_contra h
    push_neg at h
    rw [hBx] at hAB
    have h1 : A ≤ 84 := by
      by_contra h'
      push_neg at h'
      have h5 : A ^ 3 ≥ 85 ^ 3 := by
        have h2 : A ≥ 85 := by omega
        have h3 : A ^ 3 ≥ 85 ^ 3 := by
          apply Nat.pow_le_pow_of_le_left
          linarith
        linarith
      nlinarith [hAB]
    interval_cases A <;> omega