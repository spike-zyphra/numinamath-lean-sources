import Mathlib

theorem number_theory_69297 : {n : ℕ | n > 0 ∧ n ∣ (2007 + n - 9)} = {n : ℕ | n ∣ 1998} := by
  ext n
  simp only [Set.mem_setOf_eq]
  constructor
  · -- Assume h: n > 0 ∧ n divides (2007 + n - 9)
    rintro ⟨hn_pos, h⟩
    have h1 : n ∣ 1998 := by
      have h3 : n ∣ (1998 + n) := by
        have : 2007 + n - 9 = 1998 + n := by
          omega
        rw [this] at h
        exact h
      have h4 : n ∣ n := by
        simp
      have h6 : n ∣ (1998 + n) - n := by
        apply Nat.dvd_sub'
        · exact h3
        · exact h4
      have h7 : (1998 + n) - n = 1998 := by
        omega
      rw [h7] at h6
      exact h6
    exact h1
  · -- Assume h: n divides 1998
    intro h
    have hn_pos : n > 0 := by
      by_contra h1
      push_neg at h1
      have h2 : n = 0 := by
        omega
      rw [h2] at h
      all_goals norm_num at h
    constructor
    · exact hn_pos
    · -- Show n divides (2007 + n - 9)
      have h1 : n ∣ (2007 + n - 9) := by
        have h2 : n ∣ (1998 + n) := by
          have h3 : n ∣ 1998 := h
          have h4 : n ∣ n := by
            simp
          have h5 : n ∣ 1998 + n := by
            apply Nat.dvd_add
            · exact h3
            · exact h4
          exact h5
        have : 2007 + n - 9 = 1998 + n := by
          omega
        rw [this]
        exact h2
      exact h1