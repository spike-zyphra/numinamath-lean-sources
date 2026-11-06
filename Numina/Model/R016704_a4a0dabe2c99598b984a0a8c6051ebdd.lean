import Mathlib

theorem number_theory_55066 :
    Set.ncard {z : ℤ | ∃ x y, z = |x - y| ∧ 100 ≤ x ∧ x ≤ 999 ∧ 100 ≤ y ∧ y ≤ 999 ∧ y = 100 * (x % 10) + 10 * ((x / 10) % 10) + (x / 100)} = 9 := by

  have h1 : {z : ℤ | ∃ x y, z = |x - y| ∧ 100 ≤ x ∧ x ≤ 999 ∧ 100 ≤ y ∧ y ≤ 999 ∧ y = 100 * (x % 10) + 10 * ((x / 10) % 10) + (x / 100)} = {0, 99, 198, 297, 396, 495, 594, 693, 792} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- First direction: all z in the left side must be in the right side
      rintro ⟨x, y, h_eq, hx1, hx2, hy1, hy2, h_eq2⟩
      rw [h_eq2] at h_eq
      have h2 : x ≥ 100 := by linarith
      have h3 : x ≤ 999 := by linarith
      have h4 : y ≥ 100 := by linarith
      have h5 : y ≤ 999 := by linarith
      interval_cases x <;> norm_num [h_eq2] at h_eq ⊢
      <;> omega
    · -- Second direction: all z in the right side must be in the left side
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- z = 0
        use 121, 121
        all_goals norm_num
      · -- z = 99
        use 211, 112
        all_goals norm_num
      · -- z = 198
        use 123, 321
        all_goals norm_num
      · -- z = 297
        use 411, 114
        all_goals norm_num
      · -- z = 396
        use 511, 115
        all_goals norm_num
      · -- z = 495
        use 611, 116
        all_goals norm_num
      · -- z = 594
        use 711, 117
        all_goals norm_num
      · -- z = 693
        use 811, 118
        all_goals norm_num
      · -- z = 792
        use 911, 119
        all_goals norm_num
  rw [h1]
  norm_num