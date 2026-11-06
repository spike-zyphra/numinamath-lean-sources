import Mathlib

/- If $a$ and $b$ are positive integers, and $756a=b^{3}$, then the minimum value of $a$ is ___          ___. -/
theorem number_theory_7960 : IsLeast {a : ℕ | 0 < a ∧ ∃ b, 756 * a = b ^ 3} 98 := by
  constructor
  · -- Show that 98 is in
    constructor
    · -- Show that 98 is positive
      norm_num
    · -- Show existence
      use 42
      all_goals norm_num
  · -- Show that 98 is the least in the set
    intro a ha
    rcases ha with ⟨ha_pos, ⟨b, hb⟩⟩
    by_contra h
    push_neg at h
    have h1 : b < 42 := by
      by_contra h2
      push_neg at h2
      have h2' : 756 * a >= (42 : ℕ) ^ 3 := by
        have h3 : b ^ 3 >= (42 : ℕ) ^ 3 := by
          have h4 : b >= (42 : ℕ) := by linarith
          exact Nat.pow_le_pow_of_le_left h4 3
        linarith [hb, h3]
      norm_num at h2'
      have h3 : a >= 98 := by
        omega
      linarith
    interval_cases b <;> omega