import Mathlib

/- Let $\mathrm{a}$ and $\mathrm{b}$ be two non-zero natural numbers. Show that


$$

\left(2^{a}-1\right) \wedge\left(2^{b}-1\right)=2^{a \wedge b}-1

$$
 -/

-- lemma that a^c - 1 % a^b - 1 = a^(c%b) - 1 for nats
lemma l_pow_sub_one_mod_pow_sub_one (a b c : ℕ) : (a ^ c - 1) % (a ^ b - 1) = a ^ (c % b) - 1 := by
  rcases eq_zero_or_pos a with rfl | ha0
  · simp [zero_pow_eq]; split_ifs <;> simp
  rcases Nat.eq_or_lt_of_le ha0 with rfl | ha1
  · simp
  rcases eq_zero_or_pos b with rfl | hb0
  · simp
  rcases lt_or_le c b with h | h
  · rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt h]
    rwa [Nat.sub_lt_sub_iff_right (Nat.one_le_pow c a ha0), Nat.pow_lt_pow_iff_right ha1]
    -- recursively use the lemma on smaller values
  · suffices a ^ (c - b + b) - 1 = a ^ (c - b) * (a ^ b - 1) + (a ^ (c - b) - 1) by
      rw [← Nat.sub_add_cancel h, Nat.add_mod_right, this, Nat.add_mod, Nat.mul_mod, Nat.mod_self,
        mul_zero, Nat.zero_mod, zero_add, Nat.mod_mod, l_pow_sub_one_mod_pow_sub_one]
    rw [← Nat.add_sub_assoc (Nat.one_le_pow (c - b) a ha0), ← mul_add_one, pow_add,
      Nat.sub_add_cancel (Nat.one_le_pow b a ha0)]

-- lemma that states result using recursion, converting 2^b - 1 to 2^(c%b) - 1
lemma l_pow_sub_one_gcd_pow_sub_one (a b c : ℕ) : Nat.gcd (a ^ b - 1) (a ^ c - 1) = a ^ Nat.gcd b c - 1 := by
  rcases eq_zero_or_pos b with rfl | hb
  · simp
  replace hb : c % b < b := Nat.mod_lt c hb
  rw [Nat.gcd_rec, l_pow_sub_one_mod_pow_sub_one, l_pow_sub_one_gcd_pow_sub_one, ← Nat.gcd_rec]


theorem number_theory_122851 (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.gcd (2^a - 1) (2^b - 1) = 2^(a.gcd b) - 1 := by
  -- just use the lemma
  apply l_pow_sub_one_gcd_pow_sub_one