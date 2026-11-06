import Mathlib

theorem number_theory_605331 : IsGreatest {n | 0 < n ∧ ∀ p, Nat.Prime p → p > 7 → n ∣ (p^6 - 1)} 504 := by
  constructor
  · -- Show that 504 is in the set
    constructor
    · norm_num
    · intro p hp hp'
      have h1 : p ^ 6 % 8 = 1 := by
        have hp1 : p % 2 = 1 := by
          by_contra h
          push_neg at h
          have : ¬ Nat.Prime p := by
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
          tauto
        have hp2 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
          omega
        rcases hp2 with (h | h | h | h) <;> norm_num [Nat.pow_mod, Nat.mul_mod, h, Nat.pow_succ] at *
      have h2 : p ^ 6 % 9 = 1 := by
        have hp1 : p % 3 = 1 ∨ p % 3 = 2 := by
          by_contra h
          push_neg at h
          have : p % 3 = 0 := by omega
          have : ¬ Nat.Prime p := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by omega) (by omega)
          tauto
        have hp2 : p % 9 = 1 ∨ p % 9 = 2 ∨ p % 9 = 4 ∨ p % 9 = 5 ∨ p % 9 = 7 ∨ p % 9 = 8 := by
          have hp3 : p % 3 = 1 ∨ p % 3 = 2 := hp1
          omega
        rcases hp2 with (h | h | h | h | h | h) <;> norm_num [Nat.pow_mod, Nat.mul_mod, h, Nat.pow_succ] at *
      have h3 : p ^ 6 % 7 = 1 := by
        have hp1 : p % 7 ≠ 0 := by
          by_contra h
          have : ¬ Nat.Prime p := by
            apply Nat.not_prime_of_dvd_of_lt (show 7 ∣ p by omega) (by omega) (by omega)
          tauto
        have hp2 : p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 3 ∨ p % 7 = 4 ∨ p % 7 = 5 ∨ p % 7 = 6 := by
          omega
        rcases hp2 with (h | h | h | h | h | h) <;> norm_num [Nat.pow_mod, Nat.mul_mod, h, Nat.pow_succ] at *
      have h4 : (p ^ 6 - 1) % 8 = 0 := by
        omega
      have h5 : (p ^ 6 - 1) % 9 = 0 := by
        omega
      have h6 : (p ^ 6 - 1) % 7 = 0 := by
        omega
      omega
  · -- Show that 504 is greatest in the set
    intro n hn
    rcases hn with ⟨hn_pos, h⟩
    have h11 := h 11 (by norm_num) (by norm_num)
    have h13 := h 13 (by norm_num) (by norm_num)
    have h17 := h 17 (by norm_num) (by norm_num)
    have h19 := h 19 (by norm_num) (by norm_num)
    norm_num at h11 h13 h17 h19
    have h2 : n ∣ 504 := by
      exact Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd h11 h13) h17) h19
    have h3 : n ≤ 504 := by 
      exact Nat.le_of_dvd (by linarith) h2
    linarith