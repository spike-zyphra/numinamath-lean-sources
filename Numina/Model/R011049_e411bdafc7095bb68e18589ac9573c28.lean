import Mathlib

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

theorem number_theory_6285 {x:ℕ}:
  589 * x ≡ 1026 [MOD 817] ↔ x ≡ 17 [MOD 43] := by
  apply Iff.intro
  · -- Assume 589 * x ≡ 1026 [MOD 817], we need to show x ≡ 17 [MOD 43]
    intro h
    norm_num [Nat.ModEq] at h ⊢
    omega
  · -- Assume x ≡ 17 [MOD 43], we need to show 589 * x ≡ 1026 [MOD 817]
    intro h
    norm_num [Nat.ModEq] at h ⊢
    omega