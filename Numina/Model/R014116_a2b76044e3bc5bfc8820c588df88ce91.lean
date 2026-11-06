import Mathlib

theorem number_theory_162061 : IsGreatest {x | ∀ a b c d : ℤ, x ∣ (b - a) * (c - b) * (d - c) * (d - a) * (c - a) * (d - b)} 12 := by
  constructor 
  · -- Show that 12 divides all such expressions
    show ∀ a b c d : ℤ, (12 : ℤ) ∣ (b - a) * (c - b) * (d - c) * (d - a) * (c - a) * (d - b)
    intro a b c d 
    have h1 : (b - a) * (c - b) * (d - c) * (d - a) * (c - a) * (d - b) % 12 = 0 := by
      have h2 : (b - a) * (c - b) * (d - c) * (d - a) * (c - a) * (d - b) % 4 = 0 := by
        have h41 : (b - a) * (c - b) * (d - c) * (d - a) * (c - a) * (d - b) % 4 = 0 := by
          have h1 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega 
          have h2 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega 
          have h3 : c % 4 = 0 ∨ c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3 := by omega 
          have h4 : d % 4 = 0 ∨ d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by omega 
          rcases h1 with (h1 | h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2 | h2) <;> 
            rcases h3 with (h3 | h3 | h3 | h3) <;> rcases h4 with (h4 | h4 | h4 | h4) <;> 
              simp [Int.mul_emod, Int.sub_emod, h1, h2, h3, h4]
          <;> omega 
        omega
      have h3 : (b - a) * (c - b) * (d - c) * (d - a) * (c - a) * (d - b) % 3 = 0 := by
        have h31 : (b - a) * (c - b) * (d - c) * (d - a) * (c - a) * (d - b) % 3 = 0 := by
          have h1 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega 
          have h2 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega 
          have h3 : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by omega 
          have h4 : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by omega 
          rcases h1 with (h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2) <;> 
            rcases h3 with (h3 | h3 | h3) <;> rcases h4 with (h4 | h4 | h4) <;> 
              simp [Int.mul_emod, Int.sub_emod, h1, h2, h3, h4]
          <;> omega 
        omega
      omega 
    exact Int.dvd_of_emod_eq_zero h1
  · -- Show that 12 is greatest 
    intro x hx
    have h1 : ∀ a b c d : ℤ, x ∣ (b - a) * (c - b) * (d - c) * (d - a) * (c - a) * (d - b) := hx
    have h2 := h1 0 1 2 3 
    norm_num at h2 
    have h3 : x ∣ 12 := by
      exact h2
    have h4 : x ≤ 12 := by 
      exact Int.le_of_dvd (by norm_num) h3 
    linarith