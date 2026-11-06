import Mathlib

theorem number_theory_179298 (a r : ℕ) (h₀ : a > 0) (h₁ : r > 0)
    (h₂ : Nat.Coprime a (a * r ^ 36)) :
    ∃ n, a * r ^ 18 = n ^ 18 := by
  have h4 : a.gcd (a * r ^ 36) = a := by 
    simp [Nat.gcd_mul_right]
  have h5 : a.gcd (a * r ^ 36) = 1 := by 
    rw [Nat.coprime_iff_gcd_eq_one] at h₂
    linarith
  have h3 : a = 1 := by 
    linarith [h4, h5]
  use r
  rw [h3]
  all_goals
    ring