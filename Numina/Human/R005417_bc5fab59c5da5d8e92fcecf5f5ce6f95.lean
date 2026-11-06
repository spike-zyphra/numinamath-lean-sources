import Mathlib

open Complex EuclideanGeometry

/-In triangle $A B C, \angle A B C$ is obtuse. Point $D$ lies on side $A C$ such that $\angle A B D$ is right, and point $E$ lies on side $A C$ between $A$ and $D$ such that $B D$ bisects $\angle E B C$. Find $C E$, given that $A C=35, B C=7$, and $B E=5$.-/
theorem geometry_608209 {A B C D E : ℂ} (htri : A = 0 ∧ C = 35 ∧ 0 < B.im)
    (hD : ∠ A B D = Real.pi / 2 ∧ ∃ d : ℝ, 0 < d ∧ d < 35 ∧ D = d)
    (hE : ∠ E B D = ∠ D B C ∧ ∃ e : ℝ, 0 < e ∧ e < D.re ∧ E = e)
    (d1 : dist B C = 7) (d2 : dist B E = 5) : dist C E = 10 := by
-- Extend the assumption `htri`, `hD` and `hE`, then simplify them
  rcases htri with ⟨hA, hC, imBpos⟩
  rcases hD with ⟨a1, ⟨d, ⟨dpos, dlt, hD⟩⟩⟩
  rcases hE with ⟨a2, ⟨e, ⟨epos, elt, hE⟩⟩⟩; simp [hD] at elt
-- Substitute $A$, $B$, $C$, $D$ and $E$ in `d1`, `d2`, `a1` and `a2`, then simplify them
  simp [dist_eq, hC, hE, abs_eq_sqrt_sq_add_sq] at d1 d2
  rw [Real.sqrt_eq_iff_eq_sq] at d1 d2; any_goals positivity
  simp [angle] at a1 a2; repeat rw [angle_eq_abs_arg] at a2
-- Simplify `a1` further to remove `Complex.arg`
  rw [angle_eq_abs_arg, abs_eq, arg_eq_pi_div_two_iff] at a1
  rw [arg_eq_neg_pi_div_two_iff, ← and_or_left] at a1
  rcases a1 with ⟨a1, imne0⟩; rw [div_re, div_add_div_same] at a1
  rw [div_eq_zero_iff, or_comm] at a1; rcases a1 with h|a1
  · simp at h; simp [h] at imne0
  simp [hA, hD] at a1; rw [← sub_eq_neg_add, sub_eq_zero, ← pow_two] at a1
-- Prove that $B.re$ is strictly between $0$ and $d$
  have : 0 < B.re * (d - B.re) := by
    rw [← a1]; exact sq_pos_of_pos imBpos
  rw [mul_pos_iff, or_comm] at this; rcases this with ⟨h, h'⟩|⟨reBpos, reBlt⟩
  · linarith only [h, h', dpos]
-- Simplify `a2` further to remove `Complex.arg`
  replace this : starRingEnd ℂ (D - B) ≠ 0 := by
    rw [map_ne_zero_iff, sub_ne_zero]; intro h
    simp [h] at imne0; exact RingHom.injective (starRingEnd ℂ)
  rw [← mul_div_mul_right _ _ this, mul_conj, div_eq_mul_inv] at a2
  norm_cast at a2; rw [arg_mul_real] at a2
  replace this : starRingEnd ℂ (C - B) ≠ 0 := by
    rw [map_ne_zero_iff, sub_ne_zero]; intro h
    simp [← h, hC] at imBpos; exact RingHom.injective (starRingEnd ℂ)
  rw [← mul_div_mul_right _ _ this, mul_conj, div_eq_mul_inv] at a2
  norm_cast at a2; rw [arg_mul_real, ← re_add_im B] at a2
  rw [map_sub, map_add, map_sub, map_add, hE, hD, hC] at a2
  simp at a2; rw [show (35:ℂ) = (35:ℝ) by rfl, conj_ofReal] at a2
  push_cast at a2; nth_rw 1 4 [← re_add_im B] at a2
  ring_nf at a2; rw [I_sq] at a2; ring_nf at a2
  rw [show B.im * I * d = B.im * d * I by ring] at a2
  rw [show B.im * I * 35 = 35 * B.im * I by ring] at a2
  norm_cast at a2; rw [arg_of_im_neg, arg_of_im_neg] at a2
  rw [abs_eq_neg_self.mpr, abs_eq_neg_self.mpr] at a2
  rw [neg_neg, neg_neg, Real.arccos_inj] at a2
  simp [abs_eq_sqrt_sq_add_sq] at a2; norm_cast at a2
  rw [div_eq_div_iff_comm] at a2; apply_fun fun t => t ^ 2 at a2
  rw [div_pow, div_pow, Real.sq_sqrt, Real.sq_sqrt] at a2
  rw [← one_add_div, ← one_add_div, add_left_cancel_iff] at a2
  rw [← div_pow, ← div_pow, sq_eq_sq_iff_abs_eq_abs] at a2
  rw [abs_eq_neg_self.mpr, abs_eq_neg_self.mpr] at a2
  rw [neg_eq_iff_eq_neg, neg_neg, div_eq_div_iff] at a2
  rw [← sub_eq_zero] at a2; ring_nf at a2
  replace this : e * B.im * d * 70 + (-(e * B.im * d ^ 2) - e * B.im * B.re * 70) + e * B.im * B.re ^ 2 + e * B.im ^ 3 +
  (-(B.im * d * B.re ^ 2 * 2) - B.im * d ^ 2 * 35) + B.im * d ^ 2 * B.re * 2 +
  B.im * B.re ^ 2 * 35 + (B.im ^ 3 * 35 - B.im ^ 3 * d * 2) = B.im * (e * d * 70 -
  e * d ^ 2 - e * B.re * 70 + e * B.re ^ 2 + e * B.im ^ 2 - d * B.re ^ 2 * 2 -
  d ^ 2 * 35 + d ^ 2 * B.re * 2 + B.re ^ 2 * 35 + B.im ^ 2 * 35 - B.im ^ 2 * d * 2) := by ring
  simp [this] at a2; rcases a2 with h|a2
  · linarith only [h, imBpos]
  clear this; rw [a1] at a2 d1 d2; ring_nf at a2 d1 d2
-- Rewrite $B.re$ in terms of $d$ from `d1`
  rw [← eq_sub_iff_add_eq', mul_comm, ← mul_sub] at d1
  norm_num at d1; rw [← eq_div_iff] at d1
-- Substitute $B.re$ in `a2`, then factorize the equation in `a2` and discuss three cases
  rw [d1] at d2 a2; have : d - 70 ≠ 0 := by linarith only [dlt]
  field_simp at d2 a2; ring_nf at a2
  replace this : e * 82320 - e * d * 6076 + e * d ^ 2 * 140 + (-(e * d ^ 3) - d * 41160) +
  (d ^ 2 * 2450 - d ^ 3 * 35) = (d - 28) * (d - 42) * (-(e + 35) * d + 70 * e) := by ring
  simp [this, or_assoc] at a2; rcases a2 with a2|h|h
  -- The first two cases fail due to positivity reason
  · rw [sub_eq_zero] at a2; rw [a2, ← sub_eq_zero] at d2
    ring_nf at d2; simp [show -31878+(e*2352-e^2*42) = -42*(e-33)*(e-23) by ring] at d2
    rcases d2 with d2|d2; linarith only [d2, a2, elt]
    rw [sub_eq_zero] at d2; rw [a2] at d1
    norm_num at d1; simp [d1, a2] at a1
    linarith only [a1, imBpos]
  · linarith only [h, dlt]
-- In the last case, we can solve for $e=25$ and substitute $C$ and $E$ in the final goal to compute the result
  rw [← sub_eq_add_neg, neg_sub_left, neg_mul, ← sub_eq_neg_add] at h
  rw [sub_eq_zero] at h; symm at h; rw [mul_comm, ← eq_div_iff] at h
  replace this : e + 35 ≠ 0 := by linarith only [epos]
  rw [h] at d2; field_simp at d2; ring_nf at d2
  rw [neg_eq_iff_eq_neg, neg_neg, ← eq_div_iff] at d2
  rw [show (61250:ℝ)/98 = 25^2 by norm_num, sq_eq_sq₀] at d2
  simp [dist_eq, hC, hE, d2]; norm_num; any_goals positivity
-- Finish the rest trivial goals, mainly checking positivities
  · linarith only [dlt]
  · simp [a1]; ring_nf; rw [← sub_eq_neg_add, sub_eq_zero]
    rw [mul_left_cancel_iff_of_pos epos]; intro h
    simp [h] at a1; linarith only [a1, imBpos]
  · simp [a1]; ring_nf; rw [← sub_eq_neg_add, sub_eq_zero]
    rw [mul_right_cancel_iff_of_pos]; intro h
    simp [h] at a1; linarith only [a1, imBpos]; norm_num
  · simp [a1]; ring_nf; nth_rw 2 [mul_comm]
    rw [mul_assoc, mul_comm, ← mul_sub]
    apply mul_nonpos_of_nonneg_of_nonpos
    · rw [← div_eq_mul_inv]; apply div_nonneg
      linarith only [imBpos]; rw [← sub_mul]
      apply mul_nonneg; exact le_of_lt reBlt
      norm_num
    linarith only [dlt]
  · simp [a1]; ring_nf; nth_rw 6 [mul_comm]
    rw [mul_assoc, mul_assoc, ← sub_mul, ← mul_sub]
    apply mul_nonpos_of_nonpos_of_nonneg
    · linarith only [elt]
    positivity
  · simp [a1]; ring_nf; rw [← sub_eq_neg_add, sub_eq_zero]
    rw [mul_right_cancel_iff_of_pos]; linarith only [reBlt]
    norm_num
  · simp [a1]; ring_nf; rw [← sub_eq_neg_add, sub_eq_zero]
    rw [mul_left_cancel_iff_of_pos epos]
    linarith only [reBlt]
  · simp [abs_eq_sqrt_sq_add_sq]; rw [le_div_iff₀]
    rw [neg_one_mul, neg_le]; apply Real.le_sqrt_of_sq_le
    rw [neg_sq, le_add_iff_nonneg_right]; positivity
    simp; norm_cast; apply add_pos_of_nonneg_of_pos
    · rw [a1]; ring_nf; replace this : -(e ^ 2 * B.re * d * 2)
      + e ^ 2 * B.re ^ 2 + e ^ 2 * d ^ 2 = e^2 * (d - B.re) ^ 2 := by ring
      rw [this]; positivity
    simp; rw [← sub_eq_add_neg, mul_comm, ← mul_sub]
    rw [mul_pow]; apply mul_pos; exact sq_pos_of_pos imBpos
    rw [sq_pos_iff]; linarith only [elt]
  · simp [abs_eq_sqrt_sq_add_sq]; rw [div_le_iff₀]
    rw [one_mul]; apply Real.le_sqrt_of_sq_le
    rw [le_add_iff_nonneg_right]; positivity
    simp; norm_cast; apply add_pos_of_nonneg_of_pos
    · rw [a1]; ring_nf; replace this : -(e ^ 2 * B.re * d * 2)
      + e ^ 2 * B.re ^ 2 + e ^ 2 * d ^ 2 = e^2 * (d - B.re) ^ 2 := by ring
      rw [this]; positivity
    simp; rw [← sub_eq_add_neg, mul_comm, ← mul_sub]
    rw [mul_pow]; apply mul_pos; exact sq_pos_of_pos imBpos
    rw [sq_pos_iff]; linarith only [elt]
  · simp [abs_eq_sqrt_sq_add_sq]; rw [le_div_iff₀]
    rw [neg_one_mul, neg_le]; apply Real.le_sqrt_of_sq_le
    rw [neg_sq, le_add_iff_nonneg_right]; positivity
    simp; norm_cast; apply add_pos_of_nonneg_of_pos
    · rw [a1]; ring_nf; replace this : -(B.re * d * 2450) + B.re ^ 2 * 1225
      + d ^ 2 * 1225 = 1225 * (d - B.re) ^ 2 := by ring
      rw [this]; positivity
    simp; rw [← sub_eq_neg_add, mul_comm, ← sub_mul]
    rw [mul_pow]; apply mul_pos
    rw [sq_pos_iff]; linarith only [dlt]
    exact sq_pos_of_pos imBpos
  · simp [abs_eq_sqrt_sq_add_sq]; rw [div_le_iff₀]
    rw [one_mul]; apply Real.le_sqrt_of_sq_le
    rw [le_add_iff_nonneg_right]; positivity
    simp; norm_cast; apply add_pos_of_nonneg_of_pos
    · rw [a1]; ring_nf; replace this : -(B.re * d * 2450) + B.re ^ 2 * 1225
      + d ^ 2 * 1225 = 1225 * (d - B.re) ^ 2 := by ring
      rw [this]; positivity
    simp; rw [← sub_eq_neg_add, mul_comm, ← sub_mul]
    rw [mul_pow]; apply mul_pos
    rw [sq_pos_iff]; linarith only [dlt]
    exact sq_pos_of_pos imBpos
  any_goals rw [neg_le, neg_zero]; apply Real.arccos_nonneg
  · simp; norm_cast; ring_nf
    rw [← sub_eq_neg_add, sub_neg, mul_lt_mul_left]
    exact dlt; exact imBpos
  · simp; norm_cast; ring_nf
    rw [mul_comm, sub_neg, mul_lt_mul_left]
    exact elt; exact imBpos
  any_goals simp; rw [sub_eq_zero]; intro h
  any_goals rw [← h] at imBpos
  any_goals simp [hC] at imBpos
  any_goals simp [hD] at imBpos
  simp [hA] at imBpos; simp [hE] at imBpos