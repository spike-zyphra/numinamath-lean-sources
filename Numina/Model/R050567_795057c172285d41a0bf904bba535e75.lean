import Mathlib

theorem number_theory_6997 :
    {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b + c = 5}.encard = 8 := by
  have h1 : {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b + c = 5} = { 
    (1, 1, 4), (1, 2, 3), (1, 3, 2), (1, 4, 1), 
    (2, 1, 3), (2, 2, 1), 
    (3, 1, 2), 
    (4, 1, 1)
  } := by
    ext ⟨a, b, c⟩
    simp 
    constructor 
    · rintro ⟨ha, hb, hc, h⟩
      have h5 : a * b < 5 := by
        omega 
      have h3 : a ≤ 4 := by 
        by_contra h3
        push_neg at h3 
        have h4 : a ≥ 5 := by omega 
        have h5 : a * b ≥ 5 := by 
          nlinarith [show b ≥ 1 by nlinarith]
        linarith 
      have h4 : b ≤ 4 := by 
        by_contra h4 
        push_neg at h4 
        have h5 : b ≥ 5 := by omega 
        have h6 : a * b ≥ 5 := by 
          nlinarith [show a ≥ 1 by nlinarith]
        linarith 
      interval_cases a <;> interval_cases b <;> omega 
    · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
      all_goals 
        simp 
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> try { trivial }