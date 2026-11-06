import Mathlib

theorem algebra_214515 : {x : ℝ | ∃ a b c : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ x = a / abs a + b / abs b + c / abs c + a * b * c / abs (a * b * c)} = {4, -4, 0} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- Assume x ∈ {a / |a| + b / |b| + c / |c| + a * b * c / |a * b * c| | a, b, c ∈ ℝ \ {0}}
    rintro ⟨a, b, c, ha, hb, hc, h_eq⟩
    have h1 : a / abs a = 1 ∨ a / abs a = -1 := by
      have h_a : abs a ≠ 0 := by
        intro h
        apply ha
        rw [abs_eq_zero] at h
        linarith
      have h2 : a / abs a = 1 ∨ a / abs a = -1 := by
        by_cases h_a_pos : a > 0
        · -- If a > 0, then |a| = a
          left
          rw [abs_of_pos h_a_pos]
          field_simp [h_a_pos]
        · -- If a ≤ 0, then a < 0 (since a ≠ 0)
          have h_a_neg : a < 0 := lt_of_le_of_ne (le_of_not_lt h_a_pos) (by
            intro h
            apply ha
            linarith)
          right
          rw [abs_of_neg h_a_neg]
          field_simp [h_a_neg]
      exact h2
    have h2 : b / abs b = 1 ∨ b / abs b = -1 := by
      have h_b : abs b ≠ 0 := by
        intro h
        apply hb
        rw [abs_eq_zero] at h
        linarith
      have h2 : b / abs b = 1 ∨ b / abs b = -1 := by
        by_cases h_b_pos : b > 0
        · -- If b > 0, then |b| = b
          left
          rw [abs_of_pos h_b_pos]
          field_simp [h_b_pos]
        · -- If b ≤ 0, then b < 0 (since b ≠ 0)
          have h_b_neg : b < 0 := lt_of_le_of_ne (le_of_not_lt h_b_pos) (by
            intro h
            apply hb
            linarith)
          right
          rw [abs_of_neg h_b_neg]
          field_simp [h_b_neg]
      exact h2
    have h3 : c / abs c = 1 ∨ c / abs c = -1 := by
      have h_c : abs c ≠ 0 := by
        intro h
        apply hc
        rw [abs_eq_zero] at h
        linarith
      have h2 : c / abs c = 1 ∨ c / abs c = -1 := by
        by_cases h_c_pos : c > 0
        · -- If c > 0, then |c| = c
          left
          rw [abs_of_pos h_c_pos]
          field_simp [h_c_pos]
        · -- If c ≤ 0, then c < 0 (since c ≠ 0)
          have h_c_neg : c < 0 := lt_of_le_of_ne (le_of_not_lt h_c_pos) (by
            intro h
            apply hc
            linarith)
          right
          rw [abs_of_neg h_c_neg]
          field_simp [h_c_neg]
      exact h2
    have h4 : a * b * c / abs (a * b * c) = (a / abs a) * (b / abs b) * (c / abs c) := by
      have h_abc : abs (a * b * c) = abs a * abs b * abs c := by
        simp [abs_mul]
      have h5 : abs a ≠ 0 := by
        intro h
        apply ha
        rw [abs_eq_zero] at h
        linarith
      have h6 : abs b ≠ 0 := by
        intro h
        apply hb
        rw [abs_eq_zero] at h
        linarith
      have h7 : abs c ≠ 0 := by
        intro h
        apply hc
        rw [abs_eq_zero] at h
        linarith
      field_simp [h5, h6, h7]
      <;> rw [h_abc]
      <;> ring
    rw [h_eq, h4]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;> 
      norm_num [h1, h2, h3] <;> 
      try { left; norm_num }
      <;> try { right; left; norm_num }
      <;> try { right; right; norm_num }
  · -- Show that 4, -4, and 0 are achievable
    rintro (rfl | rfl | rfl)
    · -- x = 4
      use 1, 1, 1
      norm_num
    · -- x = -4
      use -1, -1, -1
      norm_num
    · -- x = 0
      use 1, 1, -1
      norm_num