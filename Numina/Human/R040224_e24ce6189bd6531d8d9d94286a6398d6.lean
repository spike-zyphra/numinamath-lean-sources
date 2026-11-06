import Mathlib

/- 2. In a right-angled triangle, the lengths of the leg $a$ and the hypotenuse $c$ are expressed as two-digit integers, and both numbers use the same set of digits. The length of the leg $b$ is a positive rational number. What can the length of the hypotenuse be? (Provide all answers and prove that there are no others.) -/
theorem number_theory_159256 (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hright : a^2 + b^2 = c^2) (d e : ℕ) (hd : 0 < d ∧ d < 10) (he : 0 < e ∧ e < 10) (hdigits : a = 10 * d + e ∧ c = 10 * e + d) : c = 65 := by
--Preliminary lemmas
  have prime3 : Nat.Prime 3 := by decide
  have prime5 : Nat.Prime 5 := by decide
  have prime7 : Nat.Prime 7 := by decide
  have prime11 : Nat.Prime 11 := by decide
  have hde : d < e := by
    have : a < c := by
      rw [← pow_lt_pow_iff_left₀ (by linarith) (by linarith) (by norm_num : 2 ≠ 0), lt_iff_exists_add]
      use b ^ 2
      constructor
      · rw [gt_iff_lt, sq_pos_iff]
        linarith
      · rw [hright]
    rw [hdigits.1, hdigits.2] at this
    zify at this
    rw [← tsub_lt_iff_right (by linarith)] at this
    ring_nf at this
    rw [← lt_tsub_iff_right] at this
    ring_nf at this
    simp only [Nat.ofNat_pos, mul_lt_mul_right, Nat.cast_lt] at this
    exact this
--We use the fact that a=10d+e and c=10e+d to rewrite the equation a^2+b^2=c^2.
  rw [hdigits.1, hdigits.2] at hright
  ring_nf at hright
  zify at hright
  have eqb : (b : ℤ) ^ 2 = d * ↑e * 20 + ↑d ^ 2 + ↑e ^ 2 * 100 - (↑d * ↑e * 20 + ↑d ^ 2 * 100 + ↑e ^ 2) := by
    rw [← hright]
    ring_nf
  ring_nf at eqb
  rw [add_comm, ← sub_eq_add_neg, ← sub_mul, sq_sub_sq, (by norm_num : (99 : ℤ) = 11 * 3 * 3), ← mul_assoc] at eqb
  symm at eqb
--Since the left-hand-side is divisible by 3, we can divide the equation by 3.
  have : 3 ∣ b ^ 2 := by
    zify
    apply dvd_of_mul_left_eq at eqb
    exact eqb
  apply Nat.Prime.dvd_of_dvd_pow prime3 at this
  obtain ⟨k,hk⟩ := this
  rw [hk, mul_assoc, mul_assoc 11, ← pow_two, ← mul_assoc] at eqb
  simp only [Int.reduceMul, Nat.cast_mul, Nat.cast_ofNat] at eqb
  rw [mul_comm, mul_pow] at eqb
  simp only [Int.reducePow, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false] at eqb
--Since the left-hand-side is divisible by 11, we can divide the equation by 11.
  have : 11 ∣ k ^ 2 := by
    zify
    apply dvd_of_mul_left_eq at eqb
    exact eqb
  apply Nat.Prime.dvd_of_dvd_pow prime11 at this
  obtain ⟨m,hm⟩ := this
  rw [hm] at eqb
  simp only [Nat.cast_mul, Nat.cast_ofNat] at eqb
  rw [mul_comm, mul_pow, pow_two, mul_assoc] at eqb
  simp only [mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false] at eqb
--We obtain that 11 divides either e+d or e-d.
  have h11dvd : (11 : ℤ) ∣ e + d ∨ (11 : ℤ) ∣ e - d := by
    symm at eqb
    apply dvd_of_mul_right_eq at eqb
    rw [Prime.dvd_mul (by simp only [Int.prime_ofNat_iff]; exact prime11)] at eqb
    exact eqb
  rcases h11dvd with ⟨n, eqb1⟩ | ⟨n, eqb1⟩
--If it divides e+d, in particular we have e+d=11. We have 0 cases for e, only one of which yields a solution, namely e=6 and d=5. In that case c=65. In all the other cases, either d>e, or we obtain m^2 equal to a prime number.
  · have : n = 1 := by
      have : 0 < n := by linarith
      have : n < 10 := by linarith
      have : n = 1 := by
        interval_cases n
        all_goals linarith
      exact this
    rw [this, mul_one] at eqb1
    rw [eqb1] at eqb
    simp only [mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false] at eqb
    have hl : e ≥ 1 := by linarith
    have hu : e < 10 := by linarith
    interval_cases e
    · linarith
    · have : d = 9 := by zify; symm; rw [(by norm_num : (9 : ℤ) = (11 - 2)),tsub_eq_iff_eq_add_of_le, ← eqb1]; ring_nf; linarith
      linarith
    · have : d = 8 := by zify; symm; rw [(by norm_num : (8 : ℤ) = (11 - 3)),tsub_eq_iff_eq_add_of_le, ← eqb1]; ring_nf; linarith
      linarith
    · have : d = 7 := by zify; symm; rw [(by norm_num : (7 : ℤ) = (11 - 4)),tsub_eq_iff_eq_add_of_le, ← eqb1]; ring_nf; linarith
      linarith
    · have : d = 6 := by zify; symm; rw [(by norm_num : (6 : ℤ) = (11 - 5)),tsub_eq_iff_eq_add_of_le, ← eqb1]; ring_nf; linarith
      linarith
    · have : d = 5 := by zify; symm; rw [(by norm_num : (5 : ℤ) = (11 - 6)),tsub_eq_iff_eq_add_of_le, ← eqb1]; ring_nf; linarith
      linarith
    · have : d = 4 := by zify; symm; rw [(by norm_num : (4 : ℤ) = (11 - 7)),tsub_eq_iff_eq_add_of_le, ← eqb1]; ring_nf; linarith
      rw [this] at eqb
      ring_nf at eqb
      have Prime3 : Prime (3 : ℤ) := by simp; exact prime3
      have := Prime.not_square (Prime3)
      rw [eqb] at this
      exfalso
      apply this
      use m
      ring_nf
    · have : d = 3 := by zify; symm; rw [(by norm_num : (3 : ℤ) = (11 - 8)),tsub_eq_iff_eq_add_of_le, ← eqb1]; ring_nf; linarith
      rw [this] at eqb
      ring_nf at eqb
      have Prime5 : Prime (5 : ℤ) := by simp; exact prime5
      have := Prime.not_square (Prime5)
      rw [eqb] at this
      exfalso
      apply this
      use m
      ring_nf
    · have : d = 2 := by zify; symm; rw [(by norm_num : (2 : ℤ) = (11 - 9)),tsub_eq_iff_eq_add_of_le, ← eqb1]; ring_nf; linarith
      rw [this] at eqb
      ring_nf at eqb
      have Prime7 : Prime (7 : ℤ) := by simp; exact prime7
      have := Prime.not_square (Prime7)
      rw [eqb] at this
      exfalso
      apply this
      use m
      ring_nf
--If e-d is divisible by 11, we obtain a contradiction, since we find that e=d, or e-d greater than 10, both false.
  · exfalso
    have upbd: (e : ℤ) - d ≤ 10 := by linarith
    have lobd : (e : ℤ) - d > 0 := by linarith
    rw [eqb1] at upbd lobd
    have : n > 0 := by linarith
    have : 11 * n > 11 := by linarith
    linarith