import Mathlib

theorem number_theory_12189 : IsGreatest {n : ℕ | (Nat.digits 4 n).length = 4} 255 := by 
  constructor
  · -- First part: Show that 255 is in the set
    show (Nat.digits 4 255).length = 4
    norm_num
  · -- Second part: Show that no larger n is in the set
    intro n hn
    have h : (Nat.digits 4 n).length = 4 := hn
    have h1 : n < 256 := by
      by_contra h4
      push_neg at h4
      have h5 : (Nat.digits 4 n).length > 4 := by
        have h6 : n >= 256 := by omega
        have h7 : (Nat.digits 4 n).length > 4 := by
          have h9 : Nat.log 4 n >= 4 := by
            apply Nat.le_log_of_pow_le (by norm_num) h6
          have h10 : (Nat.digits 4 n).length = Nat.log 4 n + 1 := by
            rw [Nat.digits_len]
            all_goals omega
          omega
        linarith
      omega
    omega