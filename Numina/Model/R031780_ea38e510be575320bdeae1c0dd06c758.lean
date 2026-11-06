import Mathlib

theorem algebra_20285:
  IsGreatest {b : ℤ | ∃ a : ℤ, a * b = 1200 ∧ Odd b} 75 := by

  constructor
  · -- Show 75 is in the set.
    use 16
    all_goals
      constructor
      · -- Show that 16 * 75 = 1200
        norm_num
      · -- Show that 75 is odd
        decide
  · -- Show that if b is in the set, then b ≤ 75.
    intro b hb
    rcases hb with ⟨a, hab, h_odd⟩
    have h1 : b ≤ 75 := by
      by_contra h
      push_neg at h
      have h2 : b > 75 := h
      have h3 : b ∣ 1200 := by
        use a
        all_goals linarith
      have h4 : b ≤ 1200 := by
        apply Int.le_of_dvd (by norm_num) h3
      interval_cases b <;> norm_num at h3 h_odd hab <;> try { contradiction }
      all_goals try { contradiction }
    linarith