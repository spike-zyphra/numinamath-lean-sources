import Mathlib

theorem number_theory_181984 :
    IsLeast {x | ∃ a b : ℕ, a > 0 ∧ b > 0 ∧ a ^ b = 2 ^ 2023 ∧ x = b ^ a} 1 := by
  constructor
  · -- Show that 1 is in the set
    use 2 ^ 2023, 1
    all_goals 
      norm_num
  · -- Show that no element less than 1 is in the set
    intro x hx
    rcases hx with ⟨a, b, ha, hb, h1, hx⟩
    have h2 : b ^ a ≥ 1 := by
      have h3 : b ≥ 1 := by 
        omega
      have h4 : a ≥ 1 := by 
        omega
      have h10 : b ^ a ≥ 1 := by
        have h11 : b ^ a ≥ 1 := by
          have h12 : 1 ≤ b := by omega
          have h13 : 1 ≤ a := by omega
          have h14 : 1 ≤ b ^ a := by 
            apply Nat.one_le_pow
            all_goals
              omega
          linarith
        linarith
      linarith
    have h3' : x ≥ 1 := by
      have h4' : x = b ^ a := by
        omega
      omega
    linarith