import Mathlib

theorem number_theory_288548 {A B : ℕ} (h₀ : A + B = 2010) (h₁ : Nat.lcm A B = 14807) :
    max A B = 1139 := by
  have h2 : B = 2010 - A := by
    omega
  rw [h2] at h₀ h₁
  have h3 : A ≤ 2010 := by
    omega
  interval_cases A <;> norm_num [Nat.lcm, max_eq_left, max_eq_right] at h₁ ⊢ <;> omega