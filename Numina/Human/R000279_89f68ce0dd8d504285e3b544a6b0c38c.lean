import Mathlib

/- A number with  $2016$  zeros that is written as  $101010 \dots 0101$  is given, in which the zeros and ones alternate. Prove that this number is not prime.-/
theorem number_theory_8796 {n : ℕ} (hn : n = 2016) :
    ¬Nat.Prime (∑ i ∈ Finset.range (n + 1), 10 ^ (2 * i)) := by
  have := geom_sum_eq (show (100 : ℚ) ≠ 1 by norm_num) (n + 1)
  -- $10^{4034}-1=(10^{2017}-1)(10^{2017}+1)$
  conv_rhs at this =>
    congr
    . rw [show (100 : ℚ) = 10 ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul,
      show (1 : ℚ) = 1 ^ 2 by norm_num, sq_sub_sq]
    rw [show (100 : ℚ) - 1 = 11 * 9 by norm_num]
  have eleven_dvd : 11 ∣ 10 ^ (n + 1) + 1 := by
    zify
    have : 10 ≡ -1 [ZMOD 11] := rfl
    have := this.pow (n + 1)
    rw [show (-1)^(n+1)=-1 by rw [pow_eq_neg_one_iff, hn]; decide] at this
    symm at this
    rwa [Int.modEq_iff_dvd, sub_neg_eq_add] at this
  have nine_dvd : 9 ∣ 10 ^ (n + 1) - 1 := by
    zify
    rw [Nat.cast_sub (by change 0 < _; apply pow_pos; norm_num)]
    push_cast
    have : 10 ≡ 1 [ZMOD 9] := rfl
    have := this.pow (n + 1)
    rw [one_pow] at this
    symm at this
    rwa [Int.modEq_iff_dvd] at this
  --Let the first factor be  $a$  and the second one be  $b$ .
  --$n=\frac{a}{9}*\frac{b}{11}$ ,
  rcases eleven_dvd with ⟨a, ha⟩
  rcases nine_dvd with ⟨b, hb⟩
  --and it is obvious to check with divisibility rules that
  --both of these numbers are integers that are greater than one,
  --so  $n$  is not prime.
  have two_le_a : 2 ≤ a := by
    by_contra h
    push_neg at h
    interval_cases a
    . norm_num at ha
    rw [pow_succ, show n = n - 1 + 1 by rw [hn], pow_succ] at ha
    omega
  have two_le_b : 2 ≤ b := by
    by_contra h
    push_neg at h
    interval_cases b
    . rw [pow_succ] at hb
      omega
    rw [pow_succ, show n = n - 1 + 1 by rw [hn], pow_succ] at hb
    omega
  qify at ha hb
  rw [Nat.cast_sub (by change 0 < _; apply pow_pos; norm_num)] at hb
  push_cast at hb
  rw [ha, hb, show 11 * (a : ℚ) * (9 * b) = 11 * 9 * (a * b) by ring,
    mul_div_cancel_left₀ _ (by norm_num)] at this
  have : ∑ i ∈ Finset.range (n + 1), 10 ^ (2 * i) = a * b := by
    qify
    convert this using 1
    apply Finset.sum_congr rfl
    intros
    norm_num [pow_mul]
  rw [this, Nat.not_prime_iff_exists_dvd_lt (by nlinarith)]
  use a
  constructor
  . exact Nat.dvd_mul_right a b
  constructor
  . exact two_le_a
  nlinarith
