import Mathlib
open Finset Real

namespace algebra_96995
lemma induction_on {p : ℤ → Prop} (i : ℤ)
    (hz : p 0) (hp : ∀ i : ℕ, p i → p (i + 1)) (hn : ∀ i : ℕ, p (-i) → p (-i - 1)) : p i := by
  cases i with
  | ofNat i =>
    induction i with
    | zero => exact hz
    | succ i ih => exact hp _ ih
  | negSucc i =>
    suffices ∀ n : ℕ, p (-n) from this (i + 1)
    intro n; induction n with
    | zero => simp [hz]
    | succ n ih =>
      simp only [Int.ofNat_succ, Int.neg_add, Int.sub_eq_add_neg]
      ring_nf at *; tauto
end algebra_96995

/-- Given that $A_k = \frac {k(k - 1)}2\cos\frac {k(k - 1)\pi}2,$ find $|A_{19} + A_{20} + \cdots + A_{98}|.$ -/
theorem algebra_96995 {A : ℕ → ℝ}
(hA : ∀ k, A k = (k * (k - 1)) / 2 * cos ((k * (k - 1)) * π / 2)) :
|∑ i ∈ Icc 19 98, A i| = 40 := by
  -- k % 4 = 0
  have stp (k : ℕ) (hO : k % 4 = 0) : A k = (k * (k - 1)) / 2 := by
    have uu : 4 ∣ k := Nat.dvd_of_mod_eq_zero hO
    obtain ⟨g, gg⟩ := uu
    have sw : cos (↑k * (↑k - 1) * π / 2) = 1 := by
      rw [gg]
      push_cast
      norm_num
      rw [(by ring : 4 * ↑g * (4 * ↑g - 1) * π / 2 = (↑g * (4 * ↑g - 1)) * 2 * π)]
      obtain ⟨w, ww⟩ : ∃ w : ℤ, w = ↑g * (4 * ↑g - 1) := ⟨↑g * (4 * ↑g - 1), rfl⟩
      have : (↑w : ℝ) = (↑(↑g * (4 * ↑g - 1) : ℤ) : ℝ) := by rw [ww]
      norm_num at this
      rw [←this]
      clear * -
      -- perform induction to prove cos (2 * w * π) = 1
      induction w using algebra_96995.induction_on with
      | hz => norm_num
      | hp w IH =>
        norm_num; norm_num at IH
        ring_nf; ring_nf at IH
        rw [mul_comm π 2, Real.cos_add_two_pi]; exact IH
      | hn w IH =>
        norm_num; norm_num at IH
        ring_nf; ring_nf at IH
        rw [(by ring : -(↑w * π * 2) - π * 2 = -(↑w * π * 2 + π * 2)), Real.cos_neg, mul_comm π 2, Real.cos_add_two_pi]
        exact IH
    have := hA k
    rw [sw] at this
    norm_num at this; exact this
  -- k % 4 = 1
  have stp2 (k : ℕ) (hO : k % 4 = 1) : A k = (k * (k - 1)) / 2 := by
    have wl : k = 4 * (k / 4) + 1 := by omega
    have sw : cos (↑k * (↑k - 1) * π / 2) = 1 := by
      rw [wl]
      push_cast
      norm_num
      rw [(by ring : (4 * ↑(k / 4) + 1) * (4 * ↑(k / 4)) * π / 2 = 2 * ((4 * ↑(k / 4) + 1) * ↑(k / 4)) * π)]
      obtain ⟨w, ww⟩ : ∃ w : ℤ, w = ((4 * ↑(k / 4) + 1) * ↑(k / 4)) := ⟨((4 * ↑(k / 4) + 1) * ↑(k / 4)), rfl⟩
      have : (↑w : ℝ) = (↑(((4 * ↑(k / 4) + 1) * ↑(k / 4)) : ℤ) : ℝ) := by rw [ww]
      have stage3 : (↑w : ℝ) = ((4 * ↑(k / 4) + 1) * ↑(k / 4) : ℝ) := by
        norm_cast
      rw [←stage3]
      clear * -
      -- perform induction to prove cos (2 * w * π) = 1
      induction w using algebra_96995.induction_on with
      | hz => norm_num
      | hp w IH =>
        norm_num; norm_num at IH
        ring_nf; ring_nf at IH
        rw [mul_comm π 2, Real.cos_add_two_pi]; exact IH
      | hn w IH =>
        norm_num; norm_num at IH
        ring_nf; ring_nf at IH
        rw [(by ring : -(↑w * π * 2) - π * 2 = -(↑w * π * 2 + π * 2)), Real.cos_neg, mul_comm π 2, Real.cos_add_two_pi]
        exact IH
    have := hA k
    rw [sw] at this
    norm_num at this; exact this
  -- k % 4 = 2
  have stp3 (k : ℕ) (hO : k % 4 = 2) : A k = -(k * (k - 1)) / 2 := by
    have wl : k = 4 * (k / 4) + 2 := by omega
    have sw : cos (↑k * (↑k - 1) * π / 2) = -1 := by
      rw [wl]
      push_cast
      norm_num
      rw [(by ring : (4 * ↑(k / 4) + 2) * (4 * ↑(k / 4) + 2 - 1) * π / 2 = (2*(4*↑(k / 4)^2 + 3*↑(k / 4)) + 1) * π)]
      obtain ⟨w, ww⟩ : ∃ w : ℤ, w = 4*↑(k / 4)^2 + 3*↑(k / 4) := ⟨4*↑(k / 4)^2 + 3*↑(k / 4), rfl⟩
      have : (↑w : ℝ) = ((↑(4 * (↑(k / 4) : ℤ) ^ 2 + 3 * ↑(k / 4)) : ℤ) : ℝ) := by rw [ww]
      have stage3 : (↑w : ℝ) = (4 * ↑(k / 4) ^ 2 + 3 * ↑(k / 4) : ℝ) := by
        norm_cast
      rw [←stage3]
      clear * -
      -- perform induction to prove cos ((2 * w + 1) * π) = -1
      induction w using algebra_96995.induction_on with
      | hz => norm_num
      | hp w IH =>
        norm_num; norm_num at IH
        ring_nf; ring_nf at IH
        rw [(by ring : π * 3 = π + 2 * π), ←add_assoc, Real.cos_add_two_pi]; exact IH
      | hn w IH =>
        norm_num; norm_num at IH
        ring_nf; ring_nf at IH
        rw [(by ring : -(↑w * π * 2) - π = -((↑w * π * 2) - π + 2 * π)), Real.cos_neg, Real.cos_add_two_pi]
        rw [(by ring : -(↑w * π * 2) + π = -(↑w * π * 2 - π)), Real.cos_neg] at IH
        exact IH
    have := hA k
    rw [sw] at this
    norm_num at this
    rw [this]; ring
  -- k % 4 = 3
  have stp4 (k : ℕ) (hO : k % 4 = 3) : A k = -(k * (k - 1)) / 2 := by
    have wl : k = 4 * (k / 4) + 3 := by omega
    have sw : cos (↑k * (↑k - 1) * π / 2) = -1 := by
      rw [wl]
      push_cast
      norm_num
      rw [(by ring : (4 * ↑(k / 4) + 3) * (4 * ↑(k / 4) + 3 - 1) * π / 2 = (2*(4*(↑(k/4))^2 + 5*↑(k/4) + 1) + 1) * π)]
      obtain ⟨w, ww⟩ : ∃ w : ℤ, w = 4*(↑(k/4))^2 + 5*↑(k/4) + 1 := ⟨4*(↑(k/4))^2 + 5*↑(k/4) + 1, rfl⟩
      have : (↑w : ℝ) = ((4 * ↑(k / 4) ^ 2 + 5 * ↑(k / 4) + 1 : ℤ) : ℝ) := by rw [ww]
      have stage3 : (↑w : ℝ) = (4 * ↑(k / 4) ^ 2 + 5 * ↑(k / 4) + 1 : ℝ) := by
        norm_cast
      rw [←stage3]
      clear * -
      -- perform induction to prove cos ((2 * w + 1) * π) = -1
      induction w using algebra_96995.induction_on with
      | hz => norm_num
      | hp w IH =>
        norm_num; norm_num at IH
        ring_nf; ring_nf at IH
        rw [(by ring : π * 3 = π + 2 * π), ←add_assoc, Real.cos_add_two_pi]; exact IH
      | hn w IH =>
        norm_num; norm_num at IH
        ring_nf; ring_nf at IH
        rw [(by ring : -(↑w * π * 2) - π = -((↑w * π * 2) - π + 2 * π)), Real.cos_neg, Real.cos_add_two_pi]
        rw [(by ring : -(↑w * π * 2) + π = -(↑w * π * 2 - π)), Real.cos_neg] at IH
        exact IH
    have := hA k
    rw [sw] at this
    norm_num at this
    rw [this]; ring
  have yr (n : ℕ) : ∑ i ∈ Icc 19 (19 + 4 * n - 1), A i = -2 * n := by
    induction n with
    | zero => simp_rw [hA]; norm_num
    | succ n IH =>
      rw [(by zify [(by linarith : 19 + 4 * (n + 1) ≥ 1), (by linarith : 19 + 4 * n ≥ 1)]; ring : 19 + 4 * (n + 1) - 1 = 19 + 4 * n - 1 + 4)]
      -- unroll 4 iterations
      rw [←Nat.Icc_insert_succ_right (by omega)]
      simp only [Nat.succ_add_sub_one, mem_Icc, Nat.reduceLeDiff, add_le_iff_nonpos_right,
        nonpos_iff_eq_zero, one_ne_zero, and_false, not_false_eq_true, sum_insert, Nat.cast_add,
        Nat.cast_one, neg_mul]
      rw [←Nat.Icc_insert_succ_right (by omega)]
      simp only [Nat.succ_add_sub_one, mem_Icc, Nat.reduceLeDiff, add_le_iff_nonpos_right,
        nonpos_iff_eq_zero, one_ne_zero, and_false, not_false_eq_true, sum_insert, Nat.cast_add,
        Nat.cast_one, neg_mul]
      rw [←Nat.Icc_insert_succ_right (by omega)]
      simp only [Nat.succ_add_sub_one, mem_Icc, Nat.reduceLeDiff, add_le_iff_nonpos_right,
        nonpos_iff_eq_zero, one_ne_zero, and_false, not_false_eq_true, sum_insert, Nat.cast_add,
        Nat.cast_one, neg_mul]
      rw [←Nat.Icc_insert_succ_right (by omega)]
      simp only [Nat.succ_add_sub_one, mem_Icc, Nat.reduceLeDiff, add_le_iff_nonpos_right,
        nonpos_iff_eq_zero, one_ne_zero, and_false, not_false_eq_true, sum_insert, Nat.cast_add,
        Nat.cast_one, neg_mul]
      ring_nf
      simp only [Nat.succ_add_sub_one, neg_mul, mul_comm 4 n] at IH
      rw [IH]
      -- substitute four values
      have g1 := stp3 (22 + n * 4) (by clear * -; omega)
      have g2 := stp2 (21 + n * 4) (by clear * -; omega)
      have g3 := stp (20 + n * 4) (by clear * -; omega)
      have g4 := stp4 (19 + n * 4) (by clear * -; omega)
      rw [g1, g2, g3, g4]
      push_cast
      ring
  have := yr 20
  norm_num at this
  rw [this]
  norm_num