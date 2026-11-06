import Mathlib
open Nat Real Finset Set

theorem number_theory_600013 :
  IsGreatest {x | ∃ a b : ℤ, a > 0 ∧ b > 0 ∧ 23 * a + 29 * b = 2023 ∧ x = a ^ 2 + b ^ 2} 4457 := by 
  constructor
  · -- Show that 4457 is in the set
    use 64, 19 
    all_goals norm_num
  · -- Show that 4457 is the greatest in the set 
    intro x hx 
    rcases hx with ⟨a, b, ha, hb, h1, h2⟩ 
    have h3 : a ≤ 87 := by 
      nlinarith 
    have h4 : b ≤ 69 := by 
      nlinarith 
    interval_cases a <;> try { 
      omega 
    }
    <;> try { 
      interval_cases b <;> nlinarith 
    }