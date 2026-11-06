import Mathlib

theorem algebra_5835 :
    {(m, n) : ℤ × ℤ | m * n + n + 10 = (m - 1) ^ 2}.encard = 8 := by
  have h1 : {(m, n) : ℤ × ℤ | m * n + n + 10 = (m - 1) ^ 2} = 
          {(-7, -9), (-4, -5), (-3, -3), (-2, 1), (0, -9), (1, -5), (2, -3), (5, 1)} := by
    ext ⟨m, n⟩
    simp
    constructor
    · -- Assume (m, n) is a solution
      rintro H
      have h2 : m * n + n + 10 = (m - 1) ^ 2 := by linarith
      have h3 : m + 1 ∣ m ^ 2 - 2 * m - 9 := by
        use n
        linarith
      have h4 : m + 1 ∣ 6 := by
        have h5 : m + 1 ∣ m ^ 2 - 2 * m - 9 := h3
        have h6 : m + 1 ∣ (m + 1) * (m - 3) := by
          apply dvd_mul_right
        have h7 : m + 1 ∣ (m ^ 2 - 2 * m - 9 - (m + 1) * (m - 3)) := by
          apply Int.dvd_sub
          · exact h5
          · exact h6
        have h8 : (m ^ 2 - 2 * m - 9 - (m + 1) * (m - 3)) = -6 := by
          nlinarith
        have h9 : m + 1 ∣ -6 := by
          rw [h8] at h7
          exact h7
        have h10 : m + 1 ∣ 6 := by
          exact Int.dvd_neg.mp h9
        exact h10
      have h7 : m = 0 ∨ m = -2 ∨ m = 1 ∨ m = -3 ∨ m = 2 ∨ m = -4 ∨ m = 5 ∨ m = -7 := by
        have h11 : m + 1 ∣ 6 := h4
        have h12 : m + 1 ≤ 6 := by
          apply Int.le_of_dvd (by norm_num) h11
        have h13 : m + 1 ≥ -6 := by
          have h11' : - (m + 1) ∣ 6 := by
            exact Int.neg_dvd.2 h11
          have h11'' : - (m + 1) ≤ 6 := by
            apply Int.le_of_dvd (by norm_num) h11'
          omega
        have h14 : m ≤ 5 := by
          omega
        have h15 : m ≥ -7 := by
          omega
        interval_cases m <;> tauto
      rcases h7 with (r1 | r1 | r1 | r1 | r1 | r1 | r1 | r1)
      · -- m = 0
        have h8 : n = -9 := by
          rw [r1] at h2
          nlinarith
        simp [r1, h8]
      · -- m = -2
        have h8 : n = 1 := by
          rw [r1] at h2
          nlinarith
        simp [r1, h8]
      · -- m = 1
        have h8 : n = -5 := by
          rw [r1] at h2
          nlinarith
        simp [r1, h8]
      · -- m = -3
        have h8 : n = -3 := by
          rw [r1] at h2
          nlinarith
        simp [r1, h8]
      · -- m = 2
        have h8 : n = -3 := by
          rw [r1] at h2
          nlinarith
        simp [r1, h8]
      · -- m = -4
        have h8 : n = -5 := by
          rw [r1] at h2
          nlinarith
        simp [r1, h8]
      · -- m = 5
        have h8 : n = 1 := by
          rw [r1] at h2
          nlinarith
        simp [r1, h8]
      · -- m = -7
        have h8 : n = -9 := by
          rw [r1] at h2
          nlinarith
        simp [r1, h8]
    · -- Show that each of the pairs in the right side is a solution.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals
        norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { tauto }
  all_goals
    try { native_decide }