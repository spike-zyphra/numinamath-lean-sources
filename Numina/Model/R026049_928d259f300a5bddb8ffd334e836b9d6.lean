import Mathlib

theorem number_theory_212184 (n : ℕ) (h₀ : n < 100) (h₁ : n > 9)
    (h₂ : (Nat.digits 10 (2 * n)).length = 2) (h₃ : (Nat.digits 10 (2 * n)).headI ≠ 0)
    (h₄ : (Nat.digits 10 (2 * n)).tail.reverse.headI ≠ 0) (h₅ : (Nat.digits 10 (2 * n)).tail.reverse = [5, 4]) :
    n = 17 := by 
  interval_cases n <;> norm_num at h₂ h₃ h₄ h₅ ⊢ <;> try { simp_all }
  <;> omega