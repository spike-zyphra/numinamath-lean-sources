import Mathlib

open Complex EuclideanGeometry

/-In triangle $A B C, \angle A=2 \angle C$. Suppose that $A C=6, B C=8$, and $A B=\sqrt{a}-b$, where $a$ and $b$ are positive integers. Compute $100 a+b$.-/
theorem geometry_610301 (A B C : ℂ) (hA : A = 6) (hB : B.abs = 8) (hC : C = 0)
    (Bpos : 0 < B.im) (hang : ∠ B A C = 2 * ∠ B C A) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ (A - B).abs = √a - b ∧ 100 * a + b = 7303 := by
-- Apply the law of cosine to the angles at $A$ and $C$
  have cosBAC := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle B A C
  have cosBCA := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle B C A
  simp [dist_eq_norm, hC, hA, hB] at cosBAC cosBCA hang
  simp [hA, hB]; rw [← sub_eq_zero] at cosBAC cosBCA
-- Substitute the angle $∠ A$ to $2*∠ C$
  rw [hang, Real.cos_two_mul] at cosBAC; ring_nf at cosBAC cosBCA
-- Rewrite the cosine of $∠ C$ in terms of $Complex.abs (-6 + B)$ in the second equation and substitute it in the first equation
  rw [← neg_eq_iff_add_eq_zero, ← div_eq_iff] at cosBCA
  rw [← cosBCA] at cosBAC; field_simp at cosBAC; ring_nf at cosBAC
-- Factorize the equation and solve for $Complex.abs (-6 + B)$
  have : 258048 + Complex.abs (-6 + B) * 129408 + (-(Complex.abs (-6 + B) ^ 2 * 9216) - Complex.abs (-6 + B) ^ 3 * 4800) +
    Complex.abs (-6 + B) ^ 5 * 24 = 24 * (Complex.abs (-6 + B) + 2) * (Complex.abs (-6 + B) - 14) *
    (Complex.abs (-6 + B) + 6) * (Complex.abs (-6 + B) ^ 2 + 6 * Complex.abs (-6 + B) - 64) := by ring
  simp [this, or_assoc] at cosBAC; rcases cosBAC with h|h|h|h
  -- The first factor can't be zero by positivity
  · have : 0 < Complex.abs (-6 + B) + 2 := by positivity
    linarith only [this, h]
  -- The second factor can't be zero by the triangle inequality
  · have : Complex.abs (-6 + B) < Complex.abs (-6) + Complex.abs B := by
      repeat rw [← norm_eq_abs]
      apply norm_add_lt_of_not_sameRay; simp [sameRay_iff]; constructor
      · intro h; simp [h] at hB
      rw [show (-6:ℂ) = (-6:ℝ) by norm_cast, arg_ofReal_of_neg]
      intro h'; let h'' := h'
      apply_fun fun t => Real.tan t at h''
      rw [tan_arg, Real.tan_pi] at h''; symm at h''
      rw [div_eq_zero_iff] at h''; rcases h'' with h''|h''
      · simp [h''] at Bpos
      apply_fun fun t => Real.cos t at h'
      rw [cos_arg, Real.cos_pi, h''] at h'; simp at h'
      intro h; simp [h] at Bpos
      norm_num
    simp [hB] at this; linarith only [this, h]
  -- The third factor can't be zero by positivity
  · have : 0 < Complex.abs (-6 + B) + 6 := by positivity
    linarith only [this, h]
-- Solve for $Complex.abs (-6 + B)$ from the quadratic equation `h`
  rw [sub_eq_zero] at h; apply_fun fun t => t + 9 at h
  rw [show Complex.abs (-6 + B) ^ 2 + 6 * Complex.abs (-6 + B) + 9 = (Complex.abs (-6 + B) + 3) ^ 2 by ring] at h
  rw [show (64:ℝ)+9 = √73 ^ 2 by norm_num, pow_left_inj₀] at h
  rw [← eq_sub_iff_add_eq, neg_add_eq_sub] at h
-- Substitute $Complex.abs (-6 + B) = √73 - 3$ in `hab` to find $a=73$ and $b=3$
  rw [← norm_eq_abs] at h; rw [← norm_eq_abs, norm_sub_rev, h]
-- Compute the final result and finish the rest trivial goals
  use 73; norm_num; use 3; norm_num
  all_goals positivity