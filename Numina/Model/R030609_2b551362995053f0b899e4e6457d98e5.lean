import Mathlib

theorem algebra_170718 : 
  {(x, y) : ℝ × ℝ | x^2 + y^2 ≠ 0 ∧ x + (x + 2 * y) / (x^2 + y^2) = 2 ∧ y + (2 * x - y) / (x^2 + y^2) = 0} = {(0, 1), (2, -1)} := by
  ext ⟨x, y⟩
  simp [-one_div]
  constructor
  · -- Assume (x, y) is in the left side.
    rintro ⟨h1, h2, h3⟩
    have eq3 : x * (x^2 + y^2) + x + 2 * y = 2 * (x^2 + y^2) := by
      have h2' : (x + (x + 2 * y) / (x^2 + y^2) = 2) := h2
      field_simp [h1] at h2'
      <;> nlinarith
    have eq4 : y * (x^2 + y^2) + 2 * x - y = 0 := by
      have h3' : (y + (2 * x - y) / (x^2 + y^2) = 0) := h3
      field_simp [h1] at h3'
      <;> nlinarith
    have eq5 : (x - 0) * (x - 2) = 0 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y + 1), sq_nonneg (x - 0), sq_nonneg (y - 1), sq_pos_of_ne_zero (show (x^2 + y^2) ≠ 0 by assumption)]
    have h4 : x = 0 ∨ x = 2 := by
      cases (mul_eq_zero.mp eq5) with
      | inl h => 
        left
        linarith
      | inr h =>
        right
        linarith
    cases h4 with
    | inl hx0 =>
      have hx0' : x = 0 := hx0
      have eq5 : y^3 - y = 0 := by
        rw [hx0'] at eq4
        nlinarith
      have eq6 : y * (y^2 - 1) = 0 := by
        ring_nf at eq5 ⊢
        linarith
      cases (mul_eq_zero.mp eq6) with 
      | inl hy0 =>
        exfalso
        have hy0 : y = 0 := by linarith
        have h0 : x^2 + y^2 = 0 := by
          rw [hx0', hy0]
          norm_num
        contradiction
      | inr hy2 =>
        have eq7 : y^2 = 1 := by
          nlinarith
        have eq8 : 2 * y * (1 - y) = 0 := by
          rw [hx0'] at eq3
          nlinarith
        cases (mul_eq_zero.mp (show 2 * y * (1 - y) = 0 by linarith [eq8])) with
        | inl h =>
          exfalso
          have hy0 : y = 0 := by
            linarith
          have eq7' : y^2 = 1 := eq7
          rw [hy0] at eq7'
          norm_num at eq7'
        | inr h =>
          have hy1 : y = 1 := by linarith
          left
          exact ⟨hx0', hy1⟩
    | inr hx2 =>
      have hx2' : x = 2 := hx2
      have eq7 : 2 * (4 + y^2) + 2 + 2 * y = 2 * (4 + y^2) := by
        rw [hx2'] at eq3
        nlinarith
      have eq8 : y = -1 := by
        nlinarith
      right
      exact ⟨hx2', eq8⟩
  · -- Prove the reverse direction.
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- Check (0, 1)
      constructor
      · -- x^2 + y^2 ≠ 0
        norm_num
      constructor
      · -- First equation
        norm_num
      · -- Second equation
        norm_num
    · -- Check (2, -1)
      constructor
      · -- x^2 + y^2 ≠ 0
        norm_num
      constructor
      · -- First equation
        norm_num
      · -- Second equation
        norm_num