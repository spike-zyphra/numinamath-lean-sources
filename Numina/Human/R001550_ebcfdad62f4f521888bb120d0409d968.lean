import Mathlib

theorem Nat.dvd_eq_false_of_mod_ne_zero {m n : Nat} (h : n % m != 0) : (m ∣ n) = False := by
  simp [Nat.dvd_iff_mod_eq_zero, bne_iff_ne.mp h]

theorem Other_24556 (n : ℕ) : (7 ∣ 2 ^ n - 1 ↔ 3 ∣ n) ∧ ¬(7 ∣ (2^n + 1)):= by 
  have crux : (2^n: ZMod 7) = 2 ^ (n % 3) := by
    nth_rw 1 [← Nat.div_add_mod n 3]
    rw [pow_add, pow_mul, show (2^3 : ZMod 7) = 1 by rfl]
    ring
  simp [← ZMod.natCast_zmod_eq_zero_iff_dvd, sub_eq_zero]
  obtain h | h | h := (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2)
  all_goals rw [crux, h]; norm_num
  · simp only [ZMod.natCast_zmod_eq_zero_iff_dvd, Nat.dvd_of_mod_eq_zero h, true_and, ne_eq]; decide
  · simp only [show ¬(3 : ZMod 7) = 0 by decide, not_false_eq_true, and_true, show ¬(2 : ZMod 7) = 1 by decide, 
      ZMod.natCast_zmod_eq_zero_iff_dvd, Nat.dvd_eq_false_of_mod_ne_zero (by rw [h]; decide)]
  · simp [show ¬ (5 : ZMod 7) = 0 by decide, show ¬(4 : ZMod 7) = 1 by decide, ZMod.natCast_zmod_eq_zero_iff_dvd,
      Nat.dvd_eq_false_of_mod_ne_zero (by rw [h]; decide)]