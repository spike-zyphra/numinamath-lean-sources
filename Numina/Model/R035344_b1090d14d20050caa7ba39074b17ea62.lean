import Mathlib

theorem number_theory_130570 :
    {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ a ∣ b ∧ a + 2 * b = 1010}.encard = 3 := by
  have h1 : {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ a ∣ b ∧ a + 2 * b = 1010} = {(2, 504), (10, 500), (202, 404)} := by
    ext ⟨a, b⟩
    simp
    constructor
    · -- Forward direction: all conditions imply the specific pairs
      rintro ⟨ha, hb, hadvd, heq⟩
      have h2 : a ≤ 1010 := by
        omega
      have h3 : a ∣ 1010 := by
        have h4 : a ∣ b := hadvd
        have h5 : a ∣ 2 * b := by
          exact Dvd.dvd.mul_left h4 2
        have h6 : a ∣ a := by
          exact dvd_refl a
        have h7 : a ∣ a + 2 * b := by
          exact Dvd.dvd.add h6 h5
        have h8 : a + 2 * b = 1010 := heq
        rw [h8] at h7
        exact h7
      interval_cases a <;> try { 
        omega 
      } <;> try { 
        norm_num at hadvd heq ⊢ 
        <;> try { 
          exfalso 
          <;> try { 
            tauto 
          } <;> try { 
            omega 
          }
          <;> try { 
            tauto 
          }
        }
        <;> try { 
          exfalso 
          <;> try { 
            tauto 
          } <;> try { 
            omega 
          }
        }
        <;> try { 
          have h4' : b ≤ 505 := by
            omega
          interval_cases b <;> norm_num at hadvd heq ⊢ <;> trivial
        }
      }
    · -- Backward direction: specific pairs satisfy all conditions
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Check that (2, 504) satisfies all conditions
        constructor
        · norm_num -- 2 > 0
        constructor
        · norm_num -- 504 > 0
        constructor
        · norm_num -- 2 divides 504
        · norm_num -- 2 + 2 * 504 = 1010
      · -- Check that (10, 500) satisfies all conditions
        constructor
        · norm_num -- 10 > 0
        constructor
        · norm_num -- 500 > 0
        constructor
        · norm_num -- 10 divides 500
        · norm_num -- 10 + 2 * 500 = 1010
      · -- Check that (202, 404) satisfies all conditions
        constructor
        · norm_num -- 202 > 0
        constructor
        · norm_num -- 404 > 0
        constructor
        · norm_num -- 202 divides 404
        · norm_num -- 202 + 2 * 404 = 1010
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { 
    all_goals 
      try { 
        linarith 
      } 
    } 
  all_goals try { 
    tauto 
  }