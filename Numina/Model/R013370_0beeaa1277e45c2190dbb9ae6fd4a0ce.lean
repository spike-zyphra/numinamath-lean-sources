import Mathlib

def f (n : ℕ) := 2019 * n ^ 3 - 2019 * n

theorem number_theory_4102 :
    IsGreatest {m | ∀ n, (Nat.digits 10 n).length = 2 → m ∣ f n} 12114 := by
  constructor
  · -- Show 12114 divides f(n) for all two-digit n
    intro n hn
    have h1 : (Nat.digits 10 n).length = 2 := hn
    have h2 : n ≥ 10 := by
      by_contra h
      push_neg at h
      interval_cases n <;> norm_num at h1
    have h3 : n ≤ 99 := by
      by_contra h
      push_neg at h
      have h4 : (Nat.digits 10 n).length > 2 := by
        have h5 : n > 99 := by linarith
        have h7 : (Nat.digits 10 n).length > 2 := by
          have h6 : Nat.log 10 n ≥ 2 := by
            have : 10 ^ 2 ≤ n := by linarith
            have h8 : Nat.log 10 n ≥ 2 := by
              apply Nat.le_log_of_pow_le (by norm_num) this
            linarith
          have h7 : (Nat.digits 10 n).length = Nat.log 10 n + 1 := by
            rw [Nat.digits_len]
            all_goals omega
          omega
        linarith
      have h8 : (Nat.digits 10 n).length = 2 := h1
      omega
    interval_cases n <;> norm_num [f] <;> all_goals omega
  · -- Show that 12114 is the greatest such divisor
    intro m hm
    have h10 : ∀ n, (Nat.digits 10 n).length = 2 → m ∣ f n := hm
    have h2 := h10 10 (by norm_num)
    have h3 := h10 11 (by norm_num)
    have h4 := h10 12 (by norm_num)
    have h5 := h10 13 (by norm_num)
    have h6 := h10 14 (by norm_num)
    have h7 := h10 15 (by norm_num)
    have h8 := h10 99 (by norm_num)
    norm_num [f] at h2 h3 h4 h5 h6 h7 h8
    have h9 : m ∣ 12114 := by
      exact Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd h2 h3) h4) h5) h6) (Nat.dvd_gcd h7 h8)
    have h10 : m ≤ 12114 := by
      exact Nat.le_of_dvd (show 0 < 12114 by norm_num) h9
    linarith