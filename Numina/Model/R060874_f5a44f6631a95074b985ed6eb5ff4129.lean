import Mathlib

theorem number_theory_274861 (total_soldiers total_casualties : ℕ)
    (h₀ : (Nat.digits 10 total_soldiers).sum = 17)
    (h₁ : (Nat.digits 10 total_casualties).sum = 17) :
    total_soldiers - total_casualties ≡ 0 [ZMOD 9] := by
  have h2 : total_soldiers % 9 = (Nat.digits 10 total_soldiers).sum % 9 := by
    rw [Nat.modEq_nine_digits_sum]
    all_goals omega
  have h3 : total_casualties % 9 = (Nat.digits 10 total_casualties).sum % 9 := by
    rw [Nat.modEq_nine_digits_sum]
    all_goals omega
  rw [h₀] at h2
  rw [h₁] at h3
  have h4 : (total_soldiers : ℤ) % 9 = 8 := by
    omega
  have h5 : (total_casualties : ℤ) % 9 = 8 := by
    omega
  show (total_soldiers - total_casualties : ℤ) % 9 = 0
  omega