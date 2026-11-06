import Mathlib

theorem algebra_265959 :
    IsGreatest {x | ∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a * b * c = 16 ∧ x = a ^ b - b ^ c + c ^ a} 263 := by
  constructor 
  · -- Show 263 is in the set.
    use 8, 1, 2
    all_goals norm_num 
  · -- Show it's the greatest.
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, hneab, hneac, hnebc, heq, hx⟩
    
    have h1 : a ∣ 16 := by 
      use b * c 
      all_goals nlinarith 
    have h2 : b ∣ 16 := by 
      use a * c 
      all_goals nlinarith 
    have h3 : c ∣ 16 := by 
      use a * b 
      all_goals nlinarith

    have h4 : a ≤ 16 := by 
      exact Nat.le_of_dvd (by linarith) h1 
    have h5 : b ≤ 16 := by 
      exact Nat.le_of_dvd (by linarith) h2 
    have h6 : c ≤ 16 := by 
      exact Nat.le_of_dvd (by linarith) h3 

    interval_cases a <;> try { 
      omega 
    } 
    <;> try { 
      interval_cases b <;> norm_num at heq hx 
      <;> try { 
        omega 
      } 
      <;> try { 
        interval_cases c <;> norm_num at heq hx 
        <;> omega 
      } 
    }