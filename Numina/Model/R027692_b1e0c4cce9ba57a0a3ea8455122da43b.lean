import Mathlib

theorem algebra_195144 (c : ℕ) (h₀ : c > 0) (h₁ : (Nat.digits 10 c).length = 2)
    (h₂ : (Nat.digits 10 c).sum = 10) (h₃ : (Nat.digits 10 c).prod = 25) :
    c = 55 := by
  have h4 : c ≥ 10 := by
    by_contra h
    push_neg at h
    interval_cases c <;> norm_num at h₁
    all_goals omega
  have h5 : c ≤ 99 := by
    by_contra h
    push_neg at h
    have h6 : (Nat.digits 10 c).length > 2 := by
      have h7 : Nat.log 10 c ≥ 2 := by
        have h8 : c > 99 := by omega
        have h9 : 10 ^ 2 ≤ c := by linarith
        have h10 : Nat.log 10 c ≥ 2 := by
          apply Nat.le_log_of_pow_le (by norm_num) h9
        linarith
      have h8 : (Nat.digits 10 c).length > 2 := by
        have h9 : (Nat.digits 10 c).length = Nat.log 10 c + 1 := by
          rw [Nat.digits_len]
          all_goals omega
        rw [h9]
        omega
      linarith
    linarith
  interval_cases c <;> norm_num at h₁ h₂ h₃ ⊢
  <;> omega