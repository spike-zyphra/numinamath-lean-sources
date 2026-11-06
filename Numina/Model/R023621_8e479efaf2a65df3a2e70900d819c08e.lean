import Mathlib

theorem number_theory_6326 :
    IsLeast {x | 0 < x ∧ x > 2021 ∧ (7^(x - 2021)) % 50 = 1} 2025 := by
  constructor
  · -- Show that 2025 is in the set
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that no number less than 2025 is in the set
    intro x hx
    rcases hx with ⟨hx1, hx2, hx3⟩
    by_contra h
    push_neg at h
    have h1 : x < 2025 := by linarith
    have h2 : x > 2021 := by linarith
    have h3 : x = 2022 ∨ x = 2023 ∨ x = 2024 := by
      omega
    rcases h3 with (rfl | rfl | rfl)
    · -- x = 2022
      norm_num at hx3 
    · -- x = 2023
      norm_num at hx3 
    · -- x = 2024
      norm_num at hx3