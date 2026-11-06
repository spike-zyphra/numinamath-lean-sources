import Mathlib

theorem number_theory_3294 (a b : ℕ) (h₀ : a * b = 1000) (h₁ : ¬10 ∣ a) (h₂ : ¬10 ∣ b) :
    a + b = 133 := by
  have h3 : a ∣ 1000 := by
    use b 
    all_goals linarith
  have h4 : a ≤ 1000 := by 
    exact Nat.le_of_dvd (by norm_num) h3
  interval_cases a <;> omega