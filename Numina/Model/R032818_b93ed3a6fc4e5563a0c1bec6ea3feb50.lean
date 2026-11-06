import Mathlib

theorem number_theory_216781 :
    IsLeast {z : ℤ | ∃ x y : ℤ, 4 * x + 5 * y = 7 ∧ z = 5 * |x| - 3 * |y|} 1 := by
  constructor
  · -- Show that 1 is in the set
    use -2, 3
    all_goals norm_num
  · -- Show that no smaller integer is in the set
    intro z h
    rcases h with ⟨x, y, h_eq, hz⟩
    by_contra h'
    push_neg at h'
    have h1 : 5 * |x| - 3 * |y| < 1 := by
      omega
    by_cases h4 : x ≥ 0
    · -- Case x ≥ 0
      rw [abs_of_nonneg h4] at h1 hz
      by_cases h5 : y ≥ 0
      · -- Case y ≥ 0
        rw [abs_of_nonneg h5] at h1 hz
        omega
      · -- Case y < 0
        rw [abs_of_neg (not_le.mp h5)] at h1 hz
        omega
    · -- Case x < 0
      rw [abs_of_neg (not_le.mp h4) ] at h1 hz
      by_cases h5 : y ≥ 0
      · -- Case y ≥ 0
        rw [abs_of_nonneg h5] at h1 hz
        omega
      · -- Case y < 0
        rw [abs_of_neg (not_le.mp h5) ] at h1 hz
        omega