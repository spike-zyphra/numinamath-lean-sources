import Mathlib

theorem number_theory_102739 (n : ℕ) (h₀ : n < 100) (h₁ : n > 9)
    (h₂ : (n % 10 = 6 ∧ 7 ∣ n) ∨ (n % 10 = 6 ∧ ¬7 ∣ n)) (h₃ : (n > 26 ∧ n % 10 = 8) ∨ (n ≤ 26 ∧ n % 10 = 8))
    (h₄ : (13 ∣ n ∧ n < 27) ∨ (¬13 ∣ n ∧ n ≥ 27)) :
    n = 91 := by 
        omega