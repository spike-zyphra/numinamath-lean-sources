import Mathlib

open Complex EuclideanGeometry

/-Let $A B C D$ be a parallelogram such that $\angle B A D=60^{\circ}$. Let $K$ and $L$ be the midpoints of $B C$ and $C D$, respectively. Assuming that $A B K L$ is a cyclic quadrilateral, find $\angle A B D$.-/
theorem geometry_239663 {A B C D K L : ℂ}
    (hpara : A = 0 ∧ (∃ b : ℝ, 0 < b ∧ B = b) ∧ C = B + D ∧ ∃ d : ℝ, 0 < d ∧ D = d * (1 / 2 + √3 / 2 * I))
    (hK : K = (B + C) / 2) (hL : L = (C + D) / 2)
    (cosp : Cospherical {A, B, K, L}) : ∠ A B D = 5 / 12 * Real.pi := by
-- Extend the parallelogram assumption `hparal` and the cospherical assumption `cosp`, then simplify them
  rcases hpara with ⟨hA, ⟨b, bpos, hB⟩, hC, ⟨d, dpos, hD⟩⟩
  simp [hB, hD] at hC; rcases cosp with ⟨O, r, hr⟩
  simp [dist_eq, hA, hB, hC, hD, hK, hL] at hr
  repeat rw [abs_eq_sqrt_sq_add_sq] at hr
  simp at hr; rcases hr with ⟨hO1, hO2, hO3, hO4⟩
  have rnonneg : 0 ≤ r := by rw [← hO1]; positivity
  rw [← pow_left_inj₀ _ _ (show 2≠0 by simp), Real.sq_sqrt] at hO1 hO2 hO3 hO4
-- Substitute $r^2$ in `hO2`, `hO3` and `hO4`, then simplify
  rw [← hO1, ← sub_eq_zero] at hO2 hO3 hO4; ring_nf at hO2 hO3 hO4
  norm_num at hO4; ring_nf at hO4
-- Rewrite $O.re$ in terms of $b$ in `hO2`, then substitute $O.re$ in `hO3` and `hO4`
  rw [neg_add_eq_zero, mul_assoc, pow_two, mul_right_inj'] at hO2
  rw [← eq_div_iff] at hO2; rw [hO2] at hO3 hO4
  ring_nf at hO3 hO4
-- Rewrite $O.im$ in terms of $b$ and $d$ in `hO4`, then substitute $O.im$ in `hO3`
  rw [← add_sub_right_comm, sub_eq_zero] at hO4
  rw [← hO4] at hO3; field_simp at hO3; ring_nf at hO3
  simp [show b * d * 2048 + (b ^ 2 * 1024 - d ^ 2 * 2048) =
  1024 * ((b + d) ^ 2 - 3 * d ^ 2) by ring] at hO3
-- Clear `hO1`, `hO2` and `hO4`, then rewrite $b$ in terms of $d$ in `hO3`
  clear hO1 hO2 hO4; rw [sub_eq_zero] at hO3
  have : 3 * d ^ 2 = (√3 * d) ^ 2 := by rw [mul_pow]; norm_num
  rw [this, pow_left_inj₀, ← eq_sub_iff_add_eq, ← sub_one_mul] at hO3
-- Substitute $A$, $B$ and $D$ in the goal, then rewrite it in terms of arg and simplify
  rw [angle, angle_eq_abs_arg]; simp [hA, hB, hD]
  replace this : -b / (d * (2⁻¹ + √3 / 2 * I) - b) = (b - d / 2 - d * √3 / 2 * I)⁻¹ * b := by
    rw [neg_div, ← div_neg]; ring
  rw [this, arg_mul_real bpos, abs_arg_inv, arg_of_im_neg]; simp
-- Substitute $b=(√3-1)*d$ and simplify
  rw [abs_eq_self.mpr, hO3]; replace this : (√3 - 1) * d - d / 2 = (√3 - 3 / 2) * d := by ring
  rw [this]; replace this : Complex.abs ((((√3 - 1) * d) : ℝ) - d / 2 - d * ↑√3 / 2 * I) =
  √((√3 - 3 / 2) ^ 2 + 3 / 4) * d := by
    simp [abs_eq_sqrt_sq_add_sq]
    rw [← pow_left_inj₀ _ _ (show 2≠0 by simp), Real.sq_sqrt]
    ring_nf; norm_num; ring_nf; rw [Real.sq_sqrt]; ring
    · rw [sub_nonneg, ← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
      rw [mul_pow]; norm_num; all_goals positivity
    all_goals positivity
-- Cancel the common factor $d$ on the numberator and the denominator, then apply `Real.arccos_eq_of_eq_cos` to convert the goal to computing a specific cosine value
  rw [this, mul_div_mul_right]; apply Real.arccos_eq_of_eq_cos
  positivity; linarith only [Real.pi_pos]
  rw [← pow_left_inj₀ _ _ (show 2≠0 by simp)]
  rw [← mul_left_cancel_iff_of_pos (show (0:ℝ)<2 by norm_num)]
-- Use double-angle formula for cosine to compute the value, the goal follows
  rw [← @sub_left_inj _ _ 1, ← Real.cos_two_mul]
  rw [show 2 * (5 / 12 * Real.pi) = Real.pi - Real.pi / 6 by ring, Real.cos_pi_sub]
  norm_num; rw [div_pow, Real.sq_sqrt]
  replace this : 0 < (√3 - 3 / 2) ^ 2 + 3 / 4 := by positivity
  field_simp; ring_nf; norm_num
  rw [show 3 = 2+1 by simp, pow_succ]; norm_num; ring
-- Finish the rest trivial goals, mainly checking positivities
  any_goals positivity
  · apply div_nonneg
    · rw [sub_nonneg, ← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
      all_goals norm_num
    positivity
  · apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    all_goals linarith only [Real.pi_pos]
  · apply Real.arccos_nonneg
  · simp; exact dpos
  · simp [hA, hB]; positivity
  simp [hB, hD]; intro h; apply_fun fun t => t.im at h
  simp at h; simp [h] at dpos