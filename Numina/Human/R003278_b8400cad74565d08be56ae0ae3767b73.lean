import Mathlib

theorem algebra_166098 : {(x,y) : ℝ×ℝ | x ≠ 0 ∧ y ≠ 0 ∧ 3 * x = 2 * y + 3 / y ∧ 3 * y = 2 * x + 3 / x} = {(-Real.sqrt 3, -Real.sqrt 3), (Real.sqrt 3, Real.sqrt 3)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · rintro ⟨hx, hy, h1, h2⟩
    have h3 : x^2 = y^2 := by
      field_simp [hx] at h1
      field_simp [hy] at h2
      nlinarith
    have h4 : x = y ∨ x = -y := by
      apply sq_eq_sq_iff_eq_or_eq_neg.mp
      linarith
    cases h4 with
    | inl hxy_eq =>
      have h5 : x^2 = 3 := by
        field_simp [hy] at h1
        rw [hxy_eq] at h1
        nlinarith
      have hx : x = Real.sqrt 3 ∨ x = -Real.sqrt 3 := by
        have h : x^2 - 3 = 0 := by linarith
        have h_factor : (x - Real.sqrt 3) * (x + Real.sqrt 3) = 0 := by
          rw [←h]
          ring_nf
          rw [Real.sq_sqrt (by norm_num)]
          linarith
        cases (mul_eq_zero.mp h_factor) with
        | inl h1 =>
          left
          linarith
        | inr h2 =>
          right
          linarith
      cases hx with
      | inl hx_pos =>
        right
        have hy_pos : y = Real.sqrt 3 := by
          rw [←hxy_eq, hx_pos]
        exact ⟨hx_pos, hy_pos⟩
      | inr hx_neg =>
        left
        have hy_neg : y = -Real.sqrt 3 := by
          rw [←hxy_eq, hx_neg]
        exact ⟨hx_neg, hy_neg⟩
    | inr hxy_neg =>
      have h5 : x^2 = -3 := by
        field_simp [hy] at h1
        rw [show y = -x from by linarith] at h1
        nlinarith
      have : x^2 ≥ 0 := sq_nonneg x
      linarith
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
      <;> rw [hx, hy]
      <;> norm_num
    · field_simp
      ring_nf
      rw [Real.sq_sqrt (by norm_num)]
      linarith
    · linarith
