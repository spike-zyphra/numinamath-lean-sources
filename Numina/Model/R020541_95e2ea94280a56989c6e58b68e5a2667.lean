import Mathlib

theorem number_theory_7825 :
  IsGreatest {x | ∃ a b c : ℤ, x = a + b + c ∧ a^3 + b^3 = c^3 ∧ -10 ≤ a ∧ a ≤ 10 ∧ -10 ≤ b ∧ b ≤ 10 ∧ -10 ≤ c ∧ c ≤ 10} 20 := by 
  constructor
  · -- Show 20 is in the set
    use 0, 10, 10
    all_goals
      norm_num
  · -- Show no value greater than 20 is in the set
    intro x hx
    rcases hx with ⟨a, b, c, h_eq, h_eq1, ha1, ha2, hb1, hb2, hc1, hc2⟩
    have h4 : a + b + c ≤ 20 := by
      interval_cases a <;> interval_cases b <;> try { 
        omega 
      } <;> try { 
        interval_cases c 
        <;> omega 
      }
    linarith