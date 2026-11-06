import Mathlib
open Real
set_option maxHeartbeats 300000
theorem inequalities_603679 (x y z w : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hw : 0 < w) :
    (x + y + z + w) * (1 / x + 1 / y + 1 / z + 1 / w) ≤
    4 + ((x * y + x * z + x * w + y * z + y * w + z * w) ^ 2) / (3 * x * y * z * w) ∧
    ((x + y + z + w) * (1 / x + 1 / y + 1 / z + 1 / w) =
     4 + ((x * y + x * z + x * w + y * z + y * w + z * w) ^ 2) / (3 * x * y * z * w) ↔
     (x = y ∧ y = z) ∨ (y = z ∧ z = w) ∨ (x = z ∧ z = w) ∨ (x = y ∧ y = w)) := by
  have hx_ne_zero : x ≠ 0 := ne_of_gt hx
  have hy_ne_zero : y ≠ 0 := ne_of_gt hy
  have hz_ne_zero : z ≠ 0 := ne_of_gt hz
  have hw_ne_zero : w ≠ 0 := ne_of_gt hw
  have hxyzw_ne_zero : x * y * z * w ≠ 0 := by positivity
  have h_prod_pos : 0 < x * y * z * w := by positivity
  have h_3prod_pos : 0 < 3 * x * y * z * w := by positivity
  let P1 := x*y + z*w
  let P2 := x*z + y*w
  let P3 := x*w + y*z
  let S2 := x*y + x*z + x*w + y*z + y*w + z*w
  have hS2_eq_P_sum : S2 = P1 + P2 + P3 := by ring
  constructor
  ·
    have lhs_expanded : (x + y + z + w) * (1/x + 1/y + 1/z + 1/w) =
        4 + (x/y + y/x + x/z + z/x + x/w + w/x + y/z + z/y + y/w + w/y + z/w + w/z) := by field_simp [hx, hy, hz, hw];ring_nf
    have sum_ratios_eq_fraction :
        (x/y + y/x + x/z + z/x + x/w + w/x + y/z + z/y + y/w + w/y + z/w + w/z) =
        (P1*P2 + P2*P3 + P3*P1) / (x*y*z*w) := by field_simp [hx, hy, hz, hw];ring_nf
    have S2_is_def : S2 = x * y + x * z + x * w + y * z + y * w + z * w := rfl
    rw [lhs_expanded, sum_ratios_eq_fraction,← S2_is_def, hS2_eq_P_sum]
    rw [add_le_add_iff_left]
    apply (div_le_div_iff₀ h_prod_pos h_3prod_pos).mpr
    have mul_s2 :(3 * x * y * z * w)= 3 * (x * y * z * w) := by ac_rfl
    rw [mul_s2]
    have mul_ss :(P1 * P2 + P2 * P3 + P3 * P1) * (3 * (x * y * z * w))= (P1 * P2 + P2 * P3 + P3 * P1) * 3 * (x * y * z * w):= by ac_rfl
    rw [mul_ss]
    rw [mul_le_mul_right h_prod_pos]
    rw [mul_comm]
    have key_algebraic_ineq : 3 * (P1*P2 + P2*P3 + P3*P1) ≤ (P1+P2+P3)^2 := by
      suffices 0 ≤ (P1 + P2 + P3) ^ 2 - 3 * (P1 * P2 + P2 * P3 + P3 * P1) by linarith
      have h_eq_sum_sq : (P1 + P2 + P3) ^ 2 - 3 * (P1 * P2 + P2 * P3 + P3 * P1) =
                          (1/2 : ℝ) * ((P1-P2)^2 + (P2-P3)^2 + (P3-P1)^2) := by
        ring
      rw [h_eq_sum_sq]
      apply mul_nonneg (by norm_num) (add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))
    exact key_algebraic_ineq
  ·
    let goal_equality := (x + y + z + w) * (1 / x + 1 / y + 1 / z + 1 / w) =
                         4 + (S2 ^ 2) / (3 * x * y * z * w)
    let target_P_equality := 3 * (P1*P2 + P2*P3 + P3*P1) = (P1+P2+P3)^2
    have lhs_expanded_for_eq : (x + y + z + w) * (1/x + 1/y + 1/z + 1/w) =
        4 + (P1*P2 + P2*P3 + P3*P1) / (x*y*z*w) := by
      unfold P1 P2 P3
      field_simp [hx, hy, hz, hw]
      ring
    have goal_eq_iff_target_P_eq : goal_equality ↔ target_P_equality := by
      unfold goal_equality target_P_equality
      rw [lhs_expanded_for_eq, hS2_eq_P_sum]
      rw [add_left_cancel_iff]
      rw [div_eq_div_iff hxyzw_ne_zero (ne_of_gt h_3prod_pos)]
      have he: (P1 * P2 + P2 * P3 + P3 * P1) * (3 * x * y * z * w) = (P1 * P2 + P2 * P3 + P3 * P1) * 3 * (x * y * z * w) := by ac_rfl
      rw [he]
      rw [mul_right_cancel_iff_of_pos h_prod_pos]
      ring_nf
    have target_P_eq_iff_P_all_eq : target_P_equality ↔ P1 = P2 ∧ P2 = P3 := by
      unfold target_P_equality
      constructor
      · 
        intro H
        replace H : (P1 - P2) ^ 2 + (P2 - P3) ^ 2 + (P3 - P1) ^ 2 = 0 := by 
          linarith
        have H1 : (P1 - P2) ^ 2 ≥ 0 := by positivity
        have H2 : (P2 - P3) ^ 2 ≥ 0 := by positivity
        have H3 : (P3 - P1) ^ 2 ≥ 0 := by positivity
        have H4 : (P1 - P2) ^ 2 = 0 := by linarith [H, H1, H2, H3]
        have H5 : (P2 - P3) ^ 2 = 0 := by linarith [H, H1, H2, H3]
        have H6 : (P3 - P1) ^ 2 = 0 := by linarith [H, H1, H2, H3]
        simp at H4 H5 H6
        constructor <;> linarith
      · 
        intro ⟨ha, hb⟩
        rw[ha,hb]
        ring
    have P1_eq_P2_iff_cond1 : P1 = P2 ↔ (x-w)*(y-z) = 0 := by
      unfold P1 P2
      constructor
      ·
        intro h
        linarith 
      ·
        intro h
        linarith
    have P2_eq_P3_iff_cond2 : P2 = P3 ↔ (x-y)*(z-w) = 0 := by
      unfold P3 P2
      constructor
      ·
        intro h
        linarith 
      ·
        intro h
        linarith
    have P_all_eq_iff_mul_conds_zero : P1 = P2 ∧ P2 = P3 ↔ ((x-w)*(y-z) = 0) ∧ ((x-y)*(z-w) = 0) := by
      rw [P1_eq_P2_iff_cond1, P2_eq_P3_iff_cond2]
    have mul_conds_zero_iff_or_conds :
        ((x-w)*(y-z) = 0) ∧ ((x-y)*(z-w) = 0) ↔
        (x=w ∨ y=z) ∧ (x=y ∨ z=w) := by
      constructor
      · 
        rintro ⟨h₁, h₂⟩
        have h3 : x = w ∨ y = z := by
          cases (mul_eq_zero.mp h₁) with
          | inl h₃ =>
            have : x = w := by linarith
            left; exact this
          | inr h₃ =>
            have : y = z := by linarith
            right; exact this
        have h4 : x = y ∨ z = w := by
          cases (mul_eq_zero.mp h₂) with
          | inl h₃ =>
            have : x = y := by linarith
            left; exact this
          | inr h₃ =>
            have : z = w := by linarith
            right; exact this
        exact ⟨h3, h4⟩
      · 
        rintro ⟨h1, h2⟩
        constructor
        · 
          cases h1 with
          | inl h₁l =>
            have hw : x = w := h₁l
            have eq1 : x - w = 0 := by linarith
            rw [eq1]
            ring
          | inr h₁r =>
            have hz : y = z := h₁r
            have eq1 : y - z = 0 := by linarith
            rw [eq1]
            ring
        · 
          cases h2 with
          | inl h₂l =>
            have hy : x = y := h₂l
            have eq2 : x - y = 0 := by linarith
            rw [eq2]
            ring
          | inr h₂r =>
            have hw : z = w := h₂r
            have eq2 : z - w = 0 := by linarith
            rw [eq2]
            ring
    have or_conds_iff_final_form :
        (x=w ∨ y=z) ∧ (x=y ∨ z=w) ↔
        (x = y ∧ y = z) ∨ (y = z ∧ z = w) ∨ (x = z ∧ z = w) ∨ (x = y ∧ y = w) := by
      constructor
      · 
        rintro ⟨h1, h2⟩
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> ( 
          simp_all
        )
      · 
        rintro (h | h | h | h)
        · 
          have h1 : x = y := h.1
          have h2 : y = z := h.2
          have h3 : x = z := by linarith
          have h4 : x = y ∨ z = w := by left; linarith
          have h5 : x = w ∨ y = z := by right; linarith
          exact ⟨h5, h4⟩
        · 
          have h1 : y = z := h.1
          have h2 : z = w := h.2
          have h3 : y = w := by linarith
          have h4 : x = y ∨ z = w := by right; linarith
          have h5 : x = w ∨ y = z := by right; linarith
          exact ⟨h5, h4⟩
        · 
          have h1 : x = z := h.1
          have h2 : z = w := h.2
          have h3 : x = w := by linarith
          have h4 : x = y ∨ z = w := by right; linarith
          have h5 : x = w ∨ y = z := by left; linarith
          exact ⟨h5, h4⟩
        · 
          have h1 : x = y := h.1
          have h2 : y = w := h.2
          have h3 : x = w := by linarith
          have h4 : x = y ∨ z = w := by left; linarith
          have h5 : x = w ∨ y = z := by left; linarith
          exact ⟨h5, h4⟩
    have hss : (x + y + z + w) * (1 / x + 1 / y + 1 / z + 1 / w) =
    4 + (x * y + x * z + x * w + y * z + y * w + z * w) ^ 2 / (3 * x * y * z * w) ↔ goal_equality := by rfl
    rw [hss]
    rw [goal_eq_iff_target_P_eq, target_P_eq_iff_P_all_eq, P_all_eq_iff_mul_conds_zero, mul_conds_zero_iff_or_conds, or_conds_iff_final_form]