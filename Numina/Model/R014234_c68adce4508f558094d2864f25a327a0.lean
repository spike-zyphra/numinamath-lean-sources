import Mathlib

theorem number_theory_191895 (N : ℕ) :
    (Nat.digits 10 N).sum = (Nat.digits 10 (5 * N)).sum → 9 ∣ N := by 
  intro h
  have h1 : N % 9 = (Nat.digits 10 N).sum % 9 := by 
    have h2 : (Nat.digits 10 N).sum % 9 = N % 9 := by
      rw [Nat.modEq_nine_digits_sum (N)]
      all_goals omega
    omega
  have h2 : (5 * N) % 9 = (Nat.digits 10 (5 * N)).sum % 9 := by
    have h3 : (Nat.digits 10 (5 * N)).sum % 9 = (5 * N) % 9 := by
      rw [Nat.modEq_nine_digits_sum (5 * N)]
      all_goals omega
    omega
  have h4 : (Nat.digits 10 N).sum % 9 = (Nat.digits 10 (5 * N)).sum % 9 := by
    omega
  have h7 : N % 9 = 0 := by
    omega
  have h8 : 9 ∣ N := by 
    omega
  exact h8