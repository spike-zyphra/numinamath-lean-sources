import Mathlib

open Real

/-Let $x=\frac{\sum\limits_{n=1}^{44} \cos n^\circ}{\sum\limits_{n=1}^{44} \sin n^\circ}$. What is the greatest integer that does not exceed $100x$?
-/
theorem calculus_16316 (hx : x = (∑ i ∈ Finset.range 44, cos (Real.pi * (i+1) / 180)) / (∑ i ∈ Finset.range 44, sin (Real.pi * (i+1) / 180))) :
⌊100 * x⌋ = 241 := by
-- Compute the value of $cot (pi/8)$
  have ct: cot (Real.pi/8) = 1 + sqrt 2 := by
    have : 0 < sqrt 2 := by rw [sqrt_pos]; norm_num
    rw [cot_eq_cos_div_sin]; simp
    rw [div_div_div_cancel_right₀, ← sqrt_div, sqrt_eq_iff_eq_sq]
    rw [div_eq_iff]; ring_nf
    rw [show 3=2+1 by norm_num, pow_add, pow_two, ← sqrt_mul,sqrt_mul_self]
    ring; any_goals norm_num
    · intro h'; apply_fun (fun t => (t + sqrt 2)^2) at h'
      simp at h'; linarith
    apply div_nonneg; linarith
    simp; rw [sqrt_le_iff]; norm_num; any_goals linarith
-- Prove the following auxillary trigonometric identities for later use
  have cac : ∀ s t, cos s + cos t = 2 * cos ((s+t)/2) * cos ((s-t)/2) := by
    intro s t;  rw [cos, cos]
    rw [← Complex.add_re, Complex.cos_add_cos]; norm_cast
  have sas : ∀ s t, sin s + sin t = 2 * sin ((s+t)/2) * cos ((s-t)/2) := by
    intro s t;  rw [sin, sin]
    rw [← Complex.add_re, Complex.sin_add_sin]; norm_cast
-- Simplify the expression of x by pairing up the sum in numerator and denominator
  have : x = 1 + sqrt 2 := by
    rw [hx, ← mul_div_mul_left _ _ (show (2:ℝ)≠0 by norm_num)]
    rw [two_mul, two_mul]
    nth_rewrite 1 [← Finset.sum_range_reflect]
    nth_rewrite 3 [← Finset.sum_range_reflect]
    repeat rw [← Finset.sum_add_distrib]
-- Rewrite the numerator and denominator by applying the lemmas cac and sas
    have num : (∑ x ∈ Finset.range 44, (cos (Real.pi * (↑(44 - 1 - x) + 1) / 180) + cos (Real.pi * (↑x + 1) / 180))) =
    2 * cos (Real.pi/8) * ∑ x ∈ Finset.range 44, cos ((Real.pi * (↑(44 - 1 - x) + 1) / 180 - Real.pi * (↑x + 1) / 180) / 2) := by
      rw [Finset.mul_sum, Finset.sum_congr]; rfl
      intro i hi; simp at hi
      rw [cac]; simp only [Nat.add_one_sub_one, mul_eq_mul_right_iff,
      mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false]; left
      rw [mul_div_assoc, mul_div_assoc, ← mul_add, div_add_div_same]
      norm_cast; ring_nf; simp
      have : ((43-i):ℕ)=43-(i:ℝ) := by rw [Nat.cast_sub]; norm_num; linarith
      rw [this]; ring_nf

    have den : ∑ x ∈ Finset.range 44, (sin (Real.pi * (↑(44 - 1 - x) + 1) / 180) + sin (Real.pi * (↑x + 1) / 180)) =
    2 * sin (Real.pi/8) * ∑ x ∈ Finset.range 44, cos ((Real.pi * (↑(44 - 1 - x) + 1) / 180 - Real.pi * (↑x + 1) / 180) / 2) := by
      rw [Finset.mul_sum, Finset.sum_congr]; rfl
      intro i hi; simp at hi
      rw [sas]; simp only [Nat.add_one_sub_one, mul_eq_mul_right_iff,
      mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false]; left
      rw [mul_div_assoc, mul_div_assoc, ← mul_add, div_add_div_same]
      norm_cast; ring_nf; simp
      have : ((43-i):ℕ)=43-(i:ℝ) := by rw [Nat.cast_sub]; norm_num; linarith
      rw [this]; ring_nf
-- Rewrite the numerator and denominator and simplify
    rw [num, den, mul_div_mul_right, mul_div_mul_left]
    rw [← Real.cot_eq_cos_div_sin, ct]; norm_num
-- Show the common factor we canceled is not zero by showing it is actually positive
    suffices : 0 < ∑ x ∈ Finset.range 44, cos ((Real.pi * (↑(44 - 1 - x) + 1) / 180 - Real.pi * (↑x + 1) / 180) / 2)
    linarith; apply Finset.sum_pos
    intro i hi; simp at hi; apply cos_pos_of_mem_Ioo; simp
    have : ((43-i):ℕ)=43-(i:ℝ) := by rw [Nat.cast_sub]; norm_num; linarith
    rw [this]; ring_nf
    constructor
    · rw [mul_assoc, ← mul_add, mul_lt_mul_left Real.pi_pos]
      linarith
    rw [mul_assoc, ← mul_add, mul_lt_mul_left Real.pi_pos]
    linarith; use 0; norm_num
-- Rewrite the final goal as inequalities and prove them
  rw [Int.floor_eq_iff, this]; norm_num; constructor
  · rw [← div_le_iff₀', ← sub_le_iff_le_add'] 
    rw [← pow_le_pow_iff_left _ _ (show 2≠0 by norm_num)]
    any_goals norm_num
  rw [← lt_div_iff', ← lt_sub_iff_add_lt']
  rw [← pow_lt_pow_iff_left _ _ (show 2≠0 by norm_num)]
  any_goals norm_num