import Mathlib

open Real Set
open scoped Real


lemma lemma_1 (x y : ℝ) (h₀ : cos y + cos x = sin (3 * x)) (h₁ : sin (2 * y) - sin (2 * x) = cos (4 * x) - cos (2 * x)) : sin (2 * y) = 2 * sin x * (cos x - sin (3 * x)) := by
  have h2 : sin (2 * y) = sin (2 * x) + (cos (4 * x) - cos (2 * x)) := by linarith
  have h3 : cos (4 * x) - cos (2 * x) = -2 * sin x * sin (3 * x) := by
    have h4 : cos (4 * x) - cos (2 * x) = -2 * sin (3 * x) * sin x := by
      have h5 : cos (4 * x) - cos (2 * x) = -2 * sin ( (4 * x + 2 * x) / 2 ) * sin ( (4 * x - 2 * x) / 2 ) := by
        rw [cos_sub_cos]
      have h6 : (4 * x + 2 * x) / 2 = 3 * x := by ring
      have h7 : (4 * x - 2 * x) / 2 = x := by ring
      rw [h6, h7] at h5
      linarith [h5]
    linarith [h4]
  have h5 : sin (2 * x) = 2 * sin x * cos x := by rw [sin_two_mul]
  rw [h3] at h2
  rw [h5] at h2
  linarith [h2]

lemma l_lower_bound (x y:ℝ) (h0: cos y + cos x = sin (3*x)) (h1: sin (2*y) - sin (2*x) = cos (4*x) - cos (2*x)):
  -1 - sqrt (2 + sqrt 2) / 2 ≤ sin y + sin x := by
  -- we'll modify the second equality
  have h1':= lemma_1 x y h0 h1
  -- substitute cos y from h0 and simplify
  rw [show cos x - sin (3*x) = -cos y by linarith, Real.sin_two_mul, mul_assoc, mul_assoc] at h1'
  apply congr_arg (fun t => t/2) at h1'; ring_nf at h1'
  apply congr_arg (fun t => t + cos y * sin x ) at h1'; ring_nf at h1'
  rw [mul_comm, ← mul_add] at h1'
  simp at h1'
  -- we have two cases to analyze, second one is trivial
  cases' h1' with hl hr
  rotate_left
  -- trivial but some code
  · rw [hr]; simp
    suffices -1 ≤ 0 ∧ 0 ≤ √(2+√2)/2 by linarith
    constructor
    · norm_num
    · apply div_nonneg; rotate_left; norm_num; exact sqrt_nonneg (2 + √2)
  -- we can easily solve the equation
  have hl' := hl;
  apply Real.cos_eq_zero_iff.mp at hl
  obtain ⟨k, hk⟩ := hl
  rw [add_mul, add_div, one_mul, mul_assoc, mul_comm, ← mul_div, div_self (by norm_num), mul_one] at hk
  -- let's substitute into first equation and simplity
  rw [hl', zero_add, ← Real.cos_pi_div_two_sub] at h0
  -- we get two solution branches, analyze both, nothing complex
  apply Real.cos_eq_cos_iff.mp at h0
  obtain ⟨k', hk'⟩ := h0
  cases' hk' with hl hr
  · have hx:x = π/8 - k'*π/2 := by linarith
    -- clearly -1 ≤ sin y
    rw [sub_eq_add_neg]
    gcongr; exact neg_one_le_sin y
    -- sin x needs to be found by case analysis
    rw [hx, Real.sin_sub, Real.sin_pi_div_eight, Real.cos_pi_div_eight]
    -- k is either even or odd
    have hk: Even k' ∨ Odd k' := by exact Int.even_or_odd k'
    cases' hk with he ho
    · unfold Even at he; obtain ⟨r, hr⟩ := he; ring_nf at hr
      rw [hr, Int.cast_mul, show r*(2:ℤ)*π/2=r*π by ring, Real.sin_int_mul_pi, mul_zero, sub_zero, show r*π = r*π - 0 by ring, Real.cos_int_mul_pi_sub, Real.cos_zero, mul_one]; simp
      field_simp
      gcongr
      suffices 0 ≤ √(2 - √2) * (-1) ^ r + √(2 + √2) by linarith
      suffices 0 ≤ √(2 - √2) * (-1) + √(2 + √2) ∧  √(2 - √2) * (-1) + √(2 + √2) ≤ √(2 - √2)*(-1)^r + √(2 + √2) by linarith
      constructor
      · simp; refine sqrt_le_sqrt ?_; linarith [sqrt_nonneg 2]
      · simp only [add_le_add_iff_right]; gcongr;
        have hr: Even r ∨ Odd r := by exact Int.even_or_odd r
        cases' hr with he ho
        · rw [Even.neg_one_zpow he]; norm_num
        · rw [Odd.neg_one_zpow ho]
    · unfold Odd at ho; obtain ⟨r, hr⟩ := ho
      rw [hr, Int.cast_add, Int.cast_mul, add_mul, add_div]; simp; rw [add_comm _ (π/2), show π / 2 + 2 * ↑r * π / 2 = π / 2 - (-2 * ↑r * π / 2) by ring, Real.sin_pi_div_two_sub, neg_mul, neg_mul, neg_div, Real.cos_neg,
      mul_assoc, mul_comm 2, ← mul_div, div_self (by norm_num), mul_one, show r*π = r*π - 0 by simp, Real.cos_int_mul_pi_sub, Real.cos_zero, mul_one, Real.cos_pi_div_two_sub, sub_zero, Real.sin_neg, Real.sin_int_mul_pi, neg_zero, mul_zero, zero_add]
      field_simp
      gcongr
      rw (config := {occs := .pos [2]}) [show √(2 + √2) = √(2 + √2)*1 by simp]
      gcongr
      have hr: Even r ∨ Odd r := by exact Int.even_or_odd r
      cases' hr with he ho
      · rw [Even.neg_one_zpow he]
      · rw [Odd.neg_one_zpow ho]; norm_num
  · -- we can easily solve for x
    have hx:x = π/4 - k'*π := by linarith
    rw [hk, hx, Real.sin_add_pi_div_two, show k*π = k*π-0 by simp, Real.cos_int_mul_pi_sub, Real.cos_zero, mul_one, Real.sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_four, show k'*π=k'*π-0 by simp, Real.cos_int_mul_pi_sub, Real.cos_zero, mul_one, sub_zero, Real.sin_int_mul_pi, mul_zero, sub_zero]
    rw [show -1 - √(2+√2)/2=-1 +(- √(2+√2)/2) by ring]; gcongr
    · have hr: Even k ∨ Odd k := by exact Int.even_or_odd k
      cases' hr with he ho
      · rw [Even.neg_one_zpow he]; norm_num
      · rw [Odd.neg_one_zpow ho]
    · suffices -√(2 + √2) / 2 ≤ - √2 / 2 ∧ -√2 / 2 ≤ √2 / 2 * (-1) ^ k' by linarith
      constructor
      · gcongr; simp
      · suffices 0 ≤ √2 / 2 * (1+(-1) ^ k') by linarith
        simp
        have hr: Even k' ∨ Odd k' := by exact Int.even_or_odd k'
        cases' hr with he ho
        · rw [Even.neg_one_zpow he]; norm_num
        · rw [Odd.neg_one_zpow ho]; norm_num

lemma l_lower_bound_achievable: ∃ x y: ℝ, cos y + cos x = sin (3*x) ∧
    sin (2*y) - sin (2*x) = cos (4*x) - cos (2*x) ∧
    sin y + sin x = -1 - sqrt (2 + sqrt 2) / 2 := by
  -- using the upper lemma we use y=-π/2 and x=-3π/8
  use -3*π/8, -π/2
  rw [neg_div, Real.cos_neg, Real.cos_pi_div_two, zero_add, Real.sin_neg, Real.sin_pi_div_two]; ring_nf
  rw [show π*(-9/8) =-(π/8)-π by ring, Real.sin_sub_pi, Real.sin_neg, Real.sin_neg, Real.sin_pi_div_eight, Real.sin_pi, neg_zero, zero_sub, show π*(-3/4) = π/4-π by ring, Real.sin_sub_pi, Real.sin_pi_div_four, Real.cos_sub_pi, Real.cos_pi_div_four, show π*(-3/2) = -(π/2)-π by ring, Real.cos_sub_pi, Real.cos_neg, Real.cos_pi_div_two, show π*(-3/8) = -(3*π/8) by ring, Real.cos_neg, Real.sin_neg]
  simp
  -- we just need to compute cos (3*π/8) and sin (3*π/8)
  -- cosine is easier, sine can be derived
  have h:=Real.cos_two_mul (3*π/8)
  apply congr_arg (fun t => √((t+1)/2)) at h; ring_nf at h; rw [Real.sqrt_sq (by apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le; ring_nf; apply (mul_le_mul_left (by exact pi_pos)).mpr; norm_num; apply (mul_le_mul_left (by exact pi_pos)).mpr; norm_num), show π*(3/4) = π-π/4 by ring, Real.cos_pi_sub, Real.cos_pi_div_four] at h; ring_nf
  constructor
  · rw [← h, neg_mul, mul_div, mul_one, div_div, show 1 / 2 + -(√2 / (2 * 2)) = (2-√2)/4 by ring_nf, sqrt_div, show (4:ℝ)=2^2 by ring_nf, Real.sqrt_sq (by norm_num), mul_div, mul_one];
    simp
    refine sqrt_le_iff.mpr ?_; norm_num
  · rw [Real.sin_eq_sqrt_one_sub_cos_sq (by positivity) (by linarith [pi_pos]), ← h, Real.sq_sqrt (by simp; refine (div_le_one₀ ?_).mpr ?_; norm_num; refine sqrt_le_iff.mpr ?_; norm_num)]; ring_nf
    rw [show 1 / 2 + √2 * (1 / 4) = (2 + √2) / 4 by ring_nf, sqrt_div (by apply add_nonneg; norm_num; exact sqrt_nonneg _), show (4:ℝ)=2^2 by ring_nf, Real.sqrt_sq (by norm_num), mul_div]; ring_nf

/- 4. The numbers $x$ and $y$ are such that the equalities $\cos y + \cos x = \sin 3x$ and $\sin 2y - \sin 2x = \cos 4x - \cos 2x$ hold. What is the smallest value that the sum $\sin y + \sin x$ can take? -/
theorem algebra_157369:
  IsLeast {val | ∃ x y:ℝ, cos y + cos x = sin (3*x) ∧
    sin (2*y) - sin (2*x) = cos (4*x) - cos (2*x) ∧ val = sin y + sin x}
    (-1 - sqrt (2 + sqrt 2) / 2) := by

  unfold IsLeast lowerBounds; simp
  constructor
  rotate_left
  · -- let's show that we really have the lower bound
    intro val x y h0 h1 h2; rw [h2]
    linarith [l_lower_bound x y h0 h1]
  · -- now we need to show that the lower bound is achieved
    obtain ⟨x, y, h0, h1, h2⟩ := l_lower_bound_achievable
    use x
    use y
    aesop