import Mathlib


/- if da ≡ db (mod dn), n,d are coprime, then we can cancel d. -/
lemma modEq_iff_modEq_cancel_of_coprime {a b d n: ℕ}
  (hd: d ≠ 0) (hn: n ≠ 0) (co: Nat.Coprime n d):
  d*a ≡ d*b [MOD d*n] ↔ a ≡ b [MOD n] := by
  constructor
  · intro h
    have: n = (d*n) / (Nat.gcd (d*n) d) := by
      rw [Nat.gcd_mul_right_left, mul_div_cancel_left₀ _ hd]
    rw [this]
    refine h.cancel_left_div_gcd ?_
    refine Nat.mul_pos ?_ ?_
    <;> apply Nat.zero_lt_of_ne_zero (by assumption)
  · intro h
    rw [← Nat.modEq_and_modEq_iff_modEq_mul co.symm]
    constructor
    · rw [Nat.modEq_iff_dvd]
      simp only [Nat.cast_mul, ← mul_sub]
      apply Int.dvd_mul_right
    · exact Nat.ModEq.mul rfl h

/- if ax ≡ b (mod n), then x ≡ a⁻¹ b (mod n), where a⁻¹ a ≡ 1 (mod n)  -/
lemma mul_modEq_iff_modEq_inv_mul {a b x n a_inv: ℕ}
  (h: a_inv * a ≡ 1 [MOD n]):
  a*x ≡ b [MOD n] ↔ x ≡ a_inv * b [MOD n] := by
  constructor
  · intro h1
    have h2: a_inv ≡ a_inv [MOD n] := rfl
    replace h2 := h1.mul h2
    rw [mul_assoc, mul_comm a _, mul_assoc, mul_comm b _] at h2
    apply Nat.ModEq.trans ?_ h2
    nth_rw 1 [← mul_one x]
    apply Nat.ModEq.mul rfl h.symm
  · intro h1
    have h2: a * x ≡ a * (a_inv * b) [MOD n] := by
      apply Nat.ModEq.mul rfl h1
    apply h2.trans ?_
    nth_rw 2 [← one_mul b]
    rw [← mul_assoc, mul_comm a _]
    apply h.mul rfl

/- Example 1 Solve the congruence equation $589 x \equiv 1026(\bmod 817)$. -/
theorem number_theory_6285 {x:ℕ}:
  589 * x ≡ 1026 [MOD 817] ↔ x ≡ 17 [MOD 43] := by

  -- notice that 19 divide 589,1026,817, and (817/19, 19) are coprime.
  -- so we can cancel factor 19.
  have h1: 589 * x ≡ 1026 [MOD 817] ↔ 31 * x ≡ 54 [MOD 43] := by
    have h1: 589 = 19 * 31 := by norm_num
    have h2: 1026 = 19 * 54 := by norm_num
    have h3: 817 = 19 * 43 := by norm_num
    rw [h1, h2, h3, mul_assoc]
    apply modEq_iff_modEq_cancel_of_coprime
    <;> norm_num

  -- 31, 43 are coprime, so exist unique solution (by modulo 43).
  -- after some calculations, we find 25 is inverse of 31 (by modulo 43)
  -- so solution ot 31x ≡ 54 (mod 43) is x ≡ 25 54 (mod 43) ≡ 17
  have h2: 31 * x ≡ 54 [MOD 43] ↔ x ≡ 17 [MOD 43] := by
    have: x ≡ 17 [MOD 43] ↔ x ≡ 25 * 54 [MOD 43] := by
      constructor
      all_goals
        intro h
        apply h.trans ?_
        rfl
    rw [this]
    apply mul_modEq_iff_modEq_inv_mul
    rfl

  rw [h1, h2]