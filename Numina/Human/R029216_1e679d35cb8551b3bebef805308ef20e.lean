import Mathlib

open Real
open scoped Real

/-In triangle $ABC,$ $\cot A \cot C = \frac{1}{2}$ and $\cot B \cot C = \frac{1}{18}.$  Find $\tan C.$-/
theorem calculus_16407 (A B C : Real) (hA : A ∈ Set.Ioo 0 π)
    (hB : B ∈ Set.Ioo 0 π) (hC : C ∈ Set.Ioo 0 π) (hABC : A + B + C = π)
    (hcotA : cot A * cot C = 1 / 2) (hcotB : cot B * cot C = 1 / 18) :
    tan C = 4 := by
  -- From $\cot A \cot C = \frac{1}{2},$ $\tan A \tan C = 2.$
  have atan_ctan : A.tan * C.tan = 2 := by
      rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos]
      rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin] at hcotA
      rw [←one_div_one_div 2, hcotA.symm]
      simp
      ring_nf
  -- Also, from $\cot B \cot C = \frac{1}{18},$ $\tan B \tan C = 18.$
  have btan_ctan : B.tan * C.tan = 18 := by
      rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos]
      rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin] at hcotB
      rw [←one_div_one_div 18, hcotB.symm]
      simp
      ring_nf
  have denominator_ne_zero: 1 - tan A * tan B - tan A * tan C - tan B * tan C ≠ 0 := by
    rw [btan_ctan, atan_ctan]
    intro hn
    have hn: tan A * tan B = -19 := by linarith
    have : (tan B * tan C) / (tan A * tan C) = 9 := by
      rw [btan_ctan, atan_ctan]
      linarith
    rw [←div_div, div_right_comm, ←mul_div, div_self, mul_one, div_eq_iff] at this
    rw [this, ←mul_assoc, mul_comm, ←mul_assoc, ←pow_two] at hn
    have : 0 ≤ (tan A) ^ 2 := by exact sq_nonneg (tan A)
    linarith
    intro ha
    rw [ha] at atan_ctan
    linarith
    intro hc
    rw [hc] at atan_ctan
    linarith

  -- From the addition formula for tangent, \[\tan (A + B + C) = \frac{\tan A + \tan B + \tan C - \tan A \tan B \tan C}{1 - (\tan A \tan B + \tan A \tan C + \tan B \tan C)}.\]
  have tanABC : tan (A + B + C) = ((tan A + tan B + tan C) - tan A * tan B * tan C)/(1 - (tan A * tan B + tan A * tan C + tan B * tan C)) := by
    have : ∃U, U = A + B + C := by simp
    rcases this with ⟨U, hU⟩
    have dU : U - A = B + C := by linarith
    have : tan (U - A) = tan (B + C) := by rw [dU]
    rw [tan_add', sub_eq_add_neg, tan_add'] at this
    rw [tan_neg, ←sub_eq_add_neg, mul_neg, sub_neg_eq_add] at this
    rw [div_eq_div_iff] at this
    have : tan U * (1 - tan A * tan B - tan A * tan C - tan B * tan C) = tan A + tan B + tan C - tan A * tan B * tan C := by linarith
    have := EuclideanDomain.eq_div_of_mul_eq_left ?_ this
    rw [hU] at this
    rw [this]
    ring_nf
    case intro.hb
    . rw [hU, hABC, tan_pi]
      linarith
    case intro.hd
    . rw [btan_ctan]
      linarith
    assumption
    rw [hU, hABC]
    constructor
    . intro k hπ
      rw [eq_div_iff_mul_eq (by linarith), mul_comm] at hπ
      simp at hπ
      obtain (h | h) := hπ
      . norm_cast at h
        omega
      . absurd pi_gt_three
        linarith
    . intro k hA
      rw [neg_eq_iff_eq_neg] at hA
      rw [hA, add_mul, add_div, one_mul, mul_comm (2 * _), mul_comm 2, ←mul_assoc, ←mul_div] at atan_ctan
      rw [div_self (by linarith), mul_one, tan_neg, add_comm, mul_comm π, tan_add_int_mul_pi] at atan_ctan
      rw [tan_pi_div_two, neg_zero, zero_mul] at atan_ctan
      linarith

    constructor
    . intro k hB
      rw [hB, add_mul, add_div, one_mul, mul_comm (2 * _), mul_comm 2, ←mul_assoc, ←mul_div] at btan_ctan
      rw [div_self (by linarith), mul_one, add_comm, mul_comm π, tan_add_int_mul_pi] at btan_ctan
      rw [tan_pi_div_two, zero_mul] at btan_ctan
      linarith
    . intro k hC
      rw [hC, add_mul, add_div, one_mul, mul_comm (2 * _), mul_comm 2, ←mul_assoc, ←mul_div] at btan_ctan
      rw [div_self (by linarith), mul_one, add_comm, mul_comm π, tan_add_int_mul_pi] at btan_ctan
      rw [tan_pi_div_two, mul_zero] at btan_ctan
      linarith
  -- Since $A + B + C = 180^\circ,$ this is 0.
  -- Hence, \[\tan A + \tan B + \tan C = \tan A \tan B \tan C.\]
  rw [hABC, tan_pi, eq_div_iff_mul_eq, zero_mul] at tanABC
  . -- Let $x = \tan C.$
    obtain ⟨x, hx⟩ : ∃x, x = tan C := by simp
    -- Then $\tan A = \frac{2}{x}$ and $\tan B = \frac{18}{x},$
    rw [hx.symm] at atan_ctan btan_ctan
    have x_ne_zero: x ≠ 0 := by
      intro hx
      rw [hx] at btan_ctan
      linarith
    have atan := EuclideanDomain.eq_div_of_mul_eq_left x_ne_zero atan_ctan
    have btan := EuclideanDomain.eq_div_of_mul_eq_left x_ne_zero btan_ctan
    -- so \[\frac{2}{x} + \frac{18}{x} + x = \frac{2}{x} \cdot \frac{18}{x} \cdot x.\]
    rw [Eq.comm, sub_eq_zero, hx.symm, atan, btan] at tanABC
    field_simp at tanABC
    rw [mul_assoc] at tanABC
    field_simp at tanABC
    -- This simplifies to $20 + x^2 = 36.$  Then $x^2 = 16,$ so $x = \pm 4.$
    have : (x - 4) * (x + 4) = 0 := by linarith
    simp at this
    obtain (h | h) := this
    . -- x = 4
      rw [hx.symm]
      linarith
    . -- If $x = -4,$ then $\tan A,$ $\tan B,$ $\tan C$ would all be negative.  This is impossible, because a triangle must have at least one acute angle, so $x = \boxed{4}.$
      have atan: tan A < 0 := by
        rw [atan]
        apply div_neg_of_pos_of_neg
        repeat linarith
      simp at hA hB hC
      have c : π/2 < C := by
        by_contra!
        have := tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) this
        linarith
      have a : π/2 < A := by
        by_contra!
        have := tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) this
        linarith
      linarith
  rw [←sub_sub, ←sub_sub]
  assumption
