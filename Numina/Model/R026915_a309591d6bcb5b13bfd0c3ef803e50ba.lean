import Mathlib

theorem number_theory_278494 (d : ℕ) (h₀ : d > 0) (h₁ : |(873451230 : ℤ) - d| + |(873451227 : ℤ) - d| + |(873451213 : ℤ) - d| = 29) :
    d = 873451215 ∨ d = 873451233 := by
  have h4 : (d : ℤ) ≥ (873451213 : ℤ) - 29 := by
    cases' abs_cases ((873451213 : ℤ) - (d : ℤ)) with h5 h5 <;> 
    cases' abs_cases ((873451227 : ℤ) - (d : ℤ)) with h6 h6 <;> 
    cases' abs_cases ((873451230 : ℤ) - (d : ℤ)) with h7 h7 <;> 
      omega
  have h5 : (d : ℤ) ≤ (873451230 : ℤ) + 29 := by
    cases' abs_cases ((873451230 : ℤ) - (d : ℤ)) with h6 h6 <;> 
    cases' abs_cases ((873451227 : ℤ) - (d : ℤ)) with h7 h7 <;> 
    cases' abs_cases ((873451213 : ℤ) - (d : ℤ)) with h8 h8 <;> 
      omega
  have h6 : d ≥ 873451184 := by 
    omega
  have h7 : d ≤ 873451259 := by 
    omega
  interval_cases d <;> norm_num at h₁ <;> tauto