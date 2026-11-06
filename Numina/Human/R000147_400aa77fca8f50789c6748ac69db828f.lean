import Mathlib

/- Theorem 6.10 states that if \( m \) is a positive integer and \( 2^{m}-1 \) is a prime number, then \( m \) must also be a prime number.-/
theorem number_theory_4914 (m : ℕ) (hm : 2 ≤ m) :
    Nat.Prime (2 ^ m - 1) → Nat.Prime m := by
  --we prove that if 2 ^ m - 1 is a prime number, then m must also be a prime number
  --contrapose the proposition and show that if m is composite, then 2 ^ m - 1 must be composite
  contrapose!; intro hnm; rw [Nat.prime_def_lt]; push_neg; intro hr1
  rw [Nat.prime_def_lt] at hnm; push_neg at hnm
  --rewrite m as a * b and show that 2 ^ a - 1 divides 2 ^ m - 1
  rcases hnm hm with ⟨a, ha1, ha2, ha3⟩
  rcases ha2 with ⟨b, hb⟩; use (2 ^ a - 1); constructor
  · apply @Nat.lt_of_add_lt_add_right (2 ^ a - 1) (2 ^ m - 1) 1
    rw [Nat.sub_add_cancel, Nat.sub_add_cancel, Nat.pow_lt_pow_iff_right]
    exact ha1; norm_num; apply Nat.one_le_pow; norm_num
    apply Nat.one_le_pow; norm_num
  constructor
  · rw [hb, pow_mul]
    have : 1 ^ b = 1 := by simp
    nth_rw 2 [← this]; exact nat_sub_dvd_pow_sub_pow (2 ^ a) 1 b
  by_contra hna; apply Nat.eq_add_of_sub_eq at hna; simp at hna
  nth_rw 2 [← pow_one 2] at hna; apply Nat.pow_right_injective at hna
  contradiction; norm_num; apply Nat.one_le_pow; norm_num
