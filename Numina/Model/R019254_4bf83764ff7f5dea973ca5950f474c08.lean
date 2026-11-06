import Mathlib

open Finset

theorem number_theory_304991 : 9 ∈ {x | ∃ a b : ℤ, x = a^2 - b^2} ∧ ¬10 ∈ {x | ∃ a b : ℤ, x = a^2 - b^2} := by
  constructor
  · -- Show 9 ∈ {x | ∃ a b : ℤ, x = a^2 - b^2}
    use 3, 0
    all_goals norm_num
  · -- Show ¬10 ∈ {x | ∃ a b : ℤ, x = a^2 - b^2}
    intro h
    rcases h with ⟨a, b, h1⟩
    have h2 : (a - b) * (a + b) = 10 := by
      nlinarith
    have h3 : (a - b) ∣ 10 := by
      use (a + b)
      all_goals linarith
    have h4 : (a - b) ≤ 10 := by
      apply Int.le_of_dvd (by norm_num) h3
    have h5 : (a - b) ≥ -10 := by
      have h6 : (- (a - b)) ∣ 10 := by 
        exact Int.neg_dvd.2 h3
      have h7 : (- (a - b)) ≤ 10 := by
        apply Int.le_of_dvd (by norm_num) h6
      have : - (a - b) ≥ -10 := by 
        omega
      omega
    interval_cases h6 : (a - b) <;> 
      omega