import Mathlib

theorem number_theory_217631 :
    {(a, b, c) : ℕ × ℕ × ℕ | a * b * c = 80 ∧ (a + 1) * (b + 1) * (c + 1) = 162} =
    {(2, 5, 8), (2, 8, 5), (5, 2, 8), (5, 8, 2), (8, 2, 5), (8, 5, 2)} := by
  ext ⟨a, b, c⟩
  simp
  constructor
  · -- Forward: prove (a,b,c) with both conditions must be ⊢ tuples
    rintro ⟨h1, h2⟩
    have h3 : a ∣ 80 := by
      use b * c
      nlinarith
    have h4 : a ≤ 80 := by
      exact Nat.le_of_dvd (by norm_num) h3
    have h5 : b ∣ 80 := by
      use a * c
      nlinarith
    have h6 : b ≤ 80 := by
      exact Nat.le_of_dvd (by norm_num) h5
    have h7 : c ∣ 80 := by
      use a * b
      nlinarith
    have h8 : c ≤ 80 := by
      exact Nat.le_of_dvd (by norm_num) h7

    interval_cases a <;> try { 
      omega 
    } <;> interval_cases b <;> try { 
      omega 
    }
    <;> try { 
      have : c = 2 ∨ c = 5 ∨ c = 8 := by 
        have h1' : a * b * c = 80 := h1
        omega 
      rcases this with (h | h | h)
      <;> try { 
        simp [h] at *
        all_goals omega 
      }
      all_goals try { 
        tauto 
      }
    }
  · -- Backward: prove the ⊢ tuples satisfy (a,b,c) condition
    rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · -- First and second equation
      constructor
      · norm_num
      · norm_num
    · -- First and second equation
      constructor
      · norm_num
      · norm_num
    · -- First and second equation
      constructor
      · norm_num
      · norm_num
    · -- First and second equation
      constructor
      · norm_num
      · norm_num
    · -- First and second equation
      constructor
      · norm_num
      · norm_num
    · -- First and second equation
      constructor
      · norm_num
      · norm_num