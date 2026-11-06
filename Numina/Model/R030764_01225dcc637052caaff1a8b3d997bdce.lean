import Mathlib

theorem number_theory_194242 :
    {(a, b, c) : ℕ × ℕ × ℕ | a ≤ b ∧ b ≤ c ∧  a * b * c = 10000 ∧ ¬10 ∣ a ∧ ¬10 ∣ b ∧ ¬10 ∣ c}.encard = 5 := by
  have h1 : {(a, b, c) : ℕ × ℕ × ℕ | a ≤ b ∧ b ≤ c ∧  a * b * c = 10000 ∧ ¬10 ∣ a ∧ ¬10 ∣ b ∧ ¬10 ∣ c} = 
    { (1, 16, 625), (2, 8, 625), (4, 4, 625), (5, 16, 125), (16, 25, 25) } := by
    ext ⟨a, b, c⟩
    simp
    constructor
    · -- Assume (a, b, c) is in the set.
      rintro ⟨h1, h2, h3, h4, h5, h6⟩
      have h7 : a ∣ 10000 := by
        use b * c
        linarith
      have h8 : a ≤ 100 := by
        by_contra h
        push_neg at h
        have h9 : b ≥ a := by linarith
        have h10 : c ≥ b := by linarith
        have h11 : a * b * c > 10000 := by
          have h12 : a > 100 := by linarith
          have h13 : b ≥ a := by linarith
          have h14 : c ≥ b := by linarith
          have h15 : a * b ≥ 100 * 100 := by nlinarith [h12, h13]
          nlinarith [h14, show b > 0 by nlinarith, show c > 0 by nlinarith]
        nlinarith
      interval_cases a <;> try { 
        omega 
      } <;> try { 
        have h10 : b ≤ 100 := by
          nlinarith [h3, show c ≥ b from by linarith]
        interval_cases b <;> omega 
      }
    · -- Show that these are in the set.
      rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ )
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  all_goals try { native_decide }