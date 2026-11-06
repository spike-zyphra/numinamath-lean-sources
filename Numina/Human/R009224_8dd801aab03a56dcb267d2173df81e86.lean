import Mathlib

/- 3. For which positive integers \( n \) is \( \phi(n) \)
a) odd -/
theorem number_theory_4865_1 (n : ℕ) (hn : n ≠ 0) :
    Odd (n.totient) ↔ n = 1 ∨ n = 2 := by
  --we show that n.totient is odd if and only if n is 1 or 2
  --show by contradiction
  by_contra ht; push_neg at ht
  --show by cases
  cases ht with
  | inl hll =>rcases hll with ⟨ht1, ht2, ht3⟩
              have r1 : 2 < n := Nat.two_lt_of_ne hn ht2 ht3
              obtain r2 := Nat.totient_even r1
              rw [← Nat.not_odd_iff_even] at r2; contradiction
  | inr hrr =>rcases hrr with ⟨hr1, hr2⟩
              cases hr2 with
              | inl h'll => rw [h'll, Nat.totient_one] at hr1
                            have : Odd 1 := by norm_num
                            contradiction
              | inr h'rr => rw [h'rr, Nat.totient_two] at hr1
                            have : Odd 1 := by norm_num
                            contradiction

/- 3. For which positive integers \( n \) is \( \phi(n) \)
b) divisible by 4 -/
-- The answer is wrong. So there is no `number_theory_4856_2`

/- 3. For which positive integers \( n \) is \( \phi(n) \)
c) equal to \( n / 2 \)?-/
theorem number_theory_4865_3 (n : ℕ) (hn1 : n ≠ 0) (hn2 : Even n) :
    n.totient = n / 2 ↔ ∃ k , 1 ≤ k ∧ n = 2 ^ k := by
  --we show that n.totient = n / 2 if and only if n is a power of 2
  --show that n can be written as m * 2 ^ k where m is odd
  have r0 : 1 ≤ padicValNat 2 n := by
    have : padicValNat 2 n ≠ 0 := by
      apply (dvd_iff_padicValNat_ne_zero hn1).mp
      apply even_iff_two_dvd.mp; exact hn2
    rw [Nat.one_le_iff_ne_zero]; exact this

  have r1 : ∃ m, Odd m ∧ n = 2 ^ (padicValNat 2 n) * m := by
    have : 2 ^ (padicValNat 2 n) ∣ n := by
      apply (padicValNat_dvd_iff_le hn1).mpr; simp
    rcases this with ⟨m, hm⟩; use m
    have t1 : ¬ 2 ^ ((padicValNat 2 n) + 1) ∣ n := by
      intro hne; rw [padicValNat_dvd_iff_le hn1] at hne; linarith
    constructor
    by_contra h'; rw [Nat.not_odd_iff_even, even_iff_two_dvd] at h'
    rcases h' with ⟨k, hk⟩; rw [hk, ← mul_assoc] at hm
    nth_rw 3 [← pow_one 2] at hm; rw [← pow_add] at hm
    have : 2 ^ (padicValNat 2 n + 1) ∣ n := by use k
    contradiction; exact hm

  rcases r1 with ⟨m, hm1, hm2⟩
  have r2 := ((Nat.coprime_pow_left_iff r0) 2 m).mpr (Nat.coprime_two_left.mpr hm1)

  constructor
  --prove that if n.totient = n / 2, then n is a power of 2., we use the multiplicative property of Euler totient function and rewrite the condition n.totient = n / 2.
  · intro ntot; rw [hm2] at ntot; nth_rw 2 [mul_comm] at ntot
    rw [Nat.mul_div_assoc] at ntot; nth_rw 5 [← pow_one 2] at ntot
    rw [Nat.pow_div, Nat.totient_mul r2, Nat.totient_prime_pow] at ntot
    simp at ntot; rw [mul_comm] at ntot
    apply Nat.mul_right_cancel (Nat.two_pow_pos (padicValNat 2 n - 1)) at ntot
    by_cases hc : 2 < m
    have := Nat.totient_even hc
    rw [ntot, ← Nat.not_odd_iff_even] at this; contradiction
    push_neg at hc; cases hc with
    | refl => rw [Nat.totient_two] at ntot; linarith
    | step hc1 => simp at hc1; rw [Nat.le_one_iff_eq_zero_or_eq_one] at hc1
                  cases hc1 with
                  | inl hll => rw [hll] at hm2; simp at hm2; contradiction
                  | inr hrr => rw [hrr] at hm2; simp at hm2; use padicValNat 2 n
    norm_num; linarith; exact r0; norm_num
    nth_rw 1 [← Nat.pow_one 2]; apply Nat.pow_dvd_pow; exact r0

  --conversely, if n is a power of 2, we prove that n.totient = n / 2
  rintro ⟨k, hk1, hk2⟩; rw [hk2, Nat.totient_prime_pow]; simp
  rw [← Nat.pow_div]; exact hk1; norm_num; norm_num; linarith
