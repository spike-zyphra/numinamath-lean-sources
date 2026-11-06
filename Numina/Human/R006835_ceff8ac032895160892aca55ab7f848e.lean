import Mathlib

open Finset


/- following is an auxilary lemma to prove (a^b-1, a^c-1) = a^(b,c) - 1.  
It's already in new mathlib, named `Nat.pow_sub_one_mod_pow_sub_one` -/
lemma l_pow_sub_one_mod_pow_sub_one (a b c : ℕ) : (a ^ c - 1) % (a ^ b - 1) = a ^ (c % b) - 1 := by
  rcases eq_zero_or_pos a with rfl| ha0
  · simp [zero_pow_eq]; split_ifs <;> simp
  rcases Nat.eq_or_lt_of_le ha0 with rfl | ha1
  · simp
  rcases eq_zero_or_pos b with rfl | hb0
  · simp
  rcases lt_or_le c b with h | h
  · rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt h]
    rwa [Nat.sub_lt_sub_iff_right (Nat.one_le_pow c a ha0), Nat.pow_lt_pow_iff_right ha1]
  · suffices a ^ (c - b + b) - 1 = a ^ (c - b) * (a ^ b - 1) + (a ^ (c - b) - 1) by
      rw [← Nat.sub_add_cancel h, Nat.add_mod_right, this, Nat.add_mod, Nat.mul_mod, Nat.mod_self,
        mul_zero, Nat.zero_mod, zero_add, Nat.mod_mod, l_pow_sub_one_mod_pow_sub_one]
    rw [← Nat.add_sub_assoc (Nat.one_le_pow (c - b) a ha0), ← mul_add_one, pow_add,
      Nat.sub_add_cancel (Nat.one_le_pow b a ha0)]

/- (a^b-1, a^c - 1) = a^(b,c) - 1. -/
lemma l_pow_sub_one_gcd_pow_sub_one (a b c : ℕ) :
    Nat.gcd (a ^ b - 1) (a ^ c - 1) = a ^ Nat.gcd b c - 1 := by
  rcases eq_zero_or_pos b with rfl | hb
  · simp
  replace hb : c % b < b := Nat.mod_lt c hb
  rw [Nat.gcd_rec, l_pow_sub_one_mod_pow_sub_one, l_pow_sub_one_gcd_pow_sub_one, ← Nat.gcd_rec]


theorem number_theory_641592 (R : ℕ → ℕ) (hR : ∀ k, R k = ∑ i ∈ Finset.range k, 10 ^ i) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : Nat.gcd (R a) (R b) = R (Nat.gcd a b) := by 
  have h1 : ∀ k, R k = (10 ^ k - 1) / 9 := by 
    intro k
    induction k with 
    | zero => 
      simp [hR]
    | succ n ih =>
      rw [hR, range_add_one, sum_insert,← hR, ih, pow_add]
      omega
      simp
  have h2 : ∀ k, R k = ((10 : ℤ) ^ k - 1) / 9 := by 
    intro k
    rw [h1]
    norm_num
  rw [h1, h1, h1]
  obtain h3 := l_pow_sub_one_gcd_pow_sub_one 10 a b
  have dvd1 : 9 ∣ 10 ^ a - 1 := by 
    zify
    rw [Nat.cast_sub]
    refine Int.ModEq.dvd ?_
    norm_num 
    have modeq1 : 1 ≡ 10 [ZMOD 9] := by 
      rfl
    rw [show (1 : ℤ) = 1 ^ a by simp]
    exact Int.ModEq.pow a modeq1
    exact Nat.one_le_pow' a 9
  have dvd2 : 9 ∣ 10 ^ b - 1 := by
    zify
    rw [Nat.cast_sub]
    refine Int.ModEq.dvd ?_
    norm_num 
    have modeq1 : 1 ≡ 10 [ZMOD 9] := by 
      rfl
    rw [show (1 : ℤ) = 1 ^ b by simp]
    exact Int.ModEq.pow b modeq1
    exact Nat.one_le_pow' b 9
  obtain h4 := Nat.gcd_div dvd1 dvd2
  rw [h3] at h4
  exact h4