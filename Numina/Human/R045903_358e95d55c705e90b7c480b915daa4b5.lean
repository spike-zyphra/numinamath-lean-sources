import Mathlib

/- define compositie natural number -/
def Nat.Composite (n : ℕ) := n ≠ 1 ∧ ¬n.Prime

/- Show that every integer greater than 11 can be expressed as the sum of two composite integers. -/
theorem number_theory_4496 {n : ℕ} (hn : n > 11) :
    ∃ c1 c2, Nat.Composite c1 ∧ Nat.Composite c2 ∧ c1 + c2 = n := by
  -- Case 1 : 2 divides n
  by_cases dvd_2 : 2 ∣ n
  · have : 2 * (n / 2 - 2) + 4 = n := by
      rw [Nat.mul_sub_left_distrib, Nat.sub_add_cancel, Nat.mul_div_cancel' dvd_2]
      rw [Nat.mul_div_cancel' dvd_2]
      omega
    refine ⟨2 * (n / 2 - 2), 4, ⟨by omega, ?_⟩, ⟨by norm_num, by decide⟩, this⟩
    apply Nat.not_prime_mul (by norm_num) (by omega)
  by_cases dvd_3 : 3 ∣ n
  -- Case 2 : 3 divides n
  · have : 3 * (n / 3 - 2) + 6 = n := by
      rw [Nat.mul_sub_left_distrib, Nat.sub_add_cancel, Nat.mul_div_cancel' dvd_3]
      rw [Nat.mul_div_cancel' dvd_3]
      omega
    refine ⟨3 * (n / 3 - 2), 6, ⟨by omega, ?_⟩, ⟨by omega, by decide⟩, this⟩
    apply Nat.not_prime_mul (by norm_num) (by omega)
  -- Case 3 : 2 and 3 both not divide n
  · rw [Nat.two_dvd_ne_zero] at dvd_2
    rw [Nat.dvd_iff_mod_eq_zero] at dvd_3
    have h := Nat.mod_lt n (show 12 > 0 by simp)
    -- Split case by the congruence class of `n` modulo 12
    replace h : n % 12 = 1 ∨ n % 12 = 5 ∨ n % 12 = 7 ∨ n % 12 = 11 := by omega
    rcases h with h | h | h | h
    · have h' : 2 * (3 * (n / 12) - 1) + 3 * (2 * (n / 12) + 1) = n := by omega
      refine ⟨2 * (3 * (n / 12) - 1), 3 * (2 * (n / 12) + 1),
        ⟨by omega, ?_⟩, ⟨by omega, ?_⟩, h'⟩ <;>
          apply Nat.not_prime_mul (by norm_num) (by omega)
    · have h' : 2 * (3 * (n / 12) + 1) + 3 * (2 * (n / 12) + 1) = n := by omega
      refine ⟨2 * (3 * (n / 12) + 1), 3 * (2 * (n / 12) + 1),
        ⟨by omega, ?_⟩, ⟨by omega, ?_⟩, h'⟩ <;>
          apply Nat.not_prime_mul (by norm_num) (by omega)
    · have h' : 2 * (3 * (n / 12) + 2) + 3 * (2 * (n / 12) + 1) = n := by omega
      refine ⟨2 * (3 * (n / 12) + 2), 3 * (2 * (n / 12) + 1),
        ⟨by omega, ?_⟩, ⟨by omega, ?_⟩, h'⟩ <;>
          apply Nat.not_prime_mul (by norm_num) (by omega)
    · have h' : 2 * (3 * (n / 12) + 1) + 3 * (2 * (n / 12) + 3) = n := by omega
      refine ⟨2 * (3 * (n / 12) + 1), 3 * (2 * (n / 12) + 3),
        ⟨by omega, ?_⟩, ⟨by omega, ?_⟩, h'⟩ <;>
          apply Nat.not_prime_mul (by norm_num) (by omega)
