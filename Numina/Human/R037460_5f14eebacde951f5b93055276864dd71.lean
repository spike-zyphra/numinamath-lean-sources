import Mathlib
open Nat

/-Given that $2018$, $106$, and $614$ have the same remainder when divided by a positive integer $n$, find the maximum value of $n$.-/
theorem number_theory_60123 : IsGreatest {n : ℕ | 0 < n ∧ 2018 % n = 106 % n ∧ 106 % n = 614 % n} 4 := by
  unfold IsGreatest
  constructor
  -- Prove $4 ∈ {n : ℕ | 0 < n ∧ 2018 % n = 106 % n ∧ 106 % n = 614 % n}$.
  · constructor
    · exact Nat.zero_lt_succ 3  -- 4 > 0
    · constructor
      · have h_mod_2018_106 : 2018 % 4 = 106 % 4 := by norm_num
        exact h_mod_2018_106
      · have h_mod_106_614 : 106 % 4 = 614 % 4 := by norm_num
        exact h_mod_106_614
  -- Prove $∀ m ∈ {n : ℕ | 0 < n ∧ 2018 % n = 106 % n ∧ 106 % n = 614 % n}$, $m ≤ 4$.
  · intro m hm
    have h_diff_2018_614 : 2018 - 614 = 1404 := by rfl
    have h_diff_614_106 : 614 - 106 = 508 := by rfl
    have h_divides : m ∣ 1404 ∧ m ∣ 508 := by
      constructor
      · have h_mod_eq_2018_614 : 2018 % m = 614 % m := by rw [hm.2.1, hm.2.2]
        have : (2018 - 614) % m = 0 := by
          rw [← Nat.sub_mod_eq_zero_of_mod_eq h_mod_eq_2018_614]
        rw [h_diff_2018_614] at this
        omega
      · have h_mod_eq_614_106 : 614 % m = 106 % m := by rw [← hm.2.2]
        have : (614 - 106) % m = 0 := by
          rw [← Nat.sub_mod_eq_zero_of_mod_eq h_mod_eq_614_106]
        rw [h_diff_614_106] at this
        omega
    have h_gcd : Nat.gcd 1404 508 = 4 := by
      have h_step1 : 1404 = 508 * 2 + 388 := by rfl
      have h_step2 : 508 = 388 * 1 + 120 := by rfl
      have h_step3 : 388 = 120 * 3 + 28 := by rfl
      have h_step4 : 120 = 28 * 4 + 8 := by rfl
      have h_step5 : 28 = 8 * 3 + 4 := by rfl
      have h_step6 : 8 = 4 * 2 + 0 := by rfl
      rw [Nat.gcd, h_step1, Nat.gcd, h_step2, Nat.gcd, h_step3, Nat.gcd, h_step4, Nat.gcd, h_step5, Nat.gcd, h_step6]
      rfl
    have h_dvd_gcd : m ∣ Nat.gcd 1404 508 := by exact Nat.dvd_gcd h_divides.1 h_divides.2
    rw [h_gcd] at h_dvd_gcd
    exact Nat.le_of_dvd (by norm_num) h_dvd_gcd