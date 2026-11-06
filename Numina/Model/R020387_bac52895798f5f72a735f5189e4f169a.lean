import Mathlib

open Real Set

lemma lemma_1 (A B C : ℝ) (h₀ : A ∈ Ioo 0 Real.pi)
  (h₁ : B ∈ Ioo 0 Real.pi) (h₂ : C ∈ Ioo 0 Real.pi) (h₃ : A + B + C = Real.pi) :
  cos A + cos B + cos C ≤ 3 / 2 := by
  rcases h₀ with ⟨h₄, h₅⟩
  rcases h₁ with  ⟨h₆, h₇⟩
  rcases h₂ with  ⟨h₈, h₉⟩
  have h₈₂ : C = Real.pi - (A + B) := by linarith [h₃]
  have h₉₂ : cos C = -cos (A + B) := by
    rw [show C = Real.pi - (A + B) by linarith]
    rw [cos_pi_sub]
  have h₄₇ : cos (A + B) = cos A * cos B - sin A * sin B := by
    rw [cos_add]
  rw [h₉₂, h₄₇]
  have h₄₇₂ : sin A > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith
    linarith
  have h₄₇₂₁ : sin B > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith
    linarith
  nlinarith [sq_nonneg (cos A - cos B), sq_nonneg (cos A - 1 / 2), sq_nonneg (cos B - 1 / 2),
    sq_nonneg (sin A - sin B), sq_nonneg (sin A - cos A), sq_nonneg (sin B - cos B),
    Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B,
    Real.sin_sq_add_cos_sq (A + B),
    sq_nonneg (sin A * sin B - 1 / 4), sq_nonneg (cos A + cos B - 1),
    Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B,
    Real.sin_sq_add_cos_sq (A + B),
    mul_pos h₄₇₂ (show 0 < sin B by apply sin_pos_of_pos_of_lt_pi; linarith; linarith)]


theorem inequalities_308258 (x y z : ℝ) (A B C : Real)
    (hA : A ∈ Set.Ioo 0 π) (hB : B ∈ Set.Ioo 0 π) (hC : C ∈ Set.Ioo 0 π)
    (hABC : A + B + C = π) :
    x^2 + y^2 + z^2 ≥ 2 * x * y * cos C + 2 * y * z * cos A + 2 * z * x * cos B := by 
  have hA1 : 0 < A := by 
    rcases hA with ⟨ha1, ha2⟩
    linarith
  have hA2 : A < Real.pi := by 
    rcases hA with ⟨ha1, ha2⟩
    linarith
  have hB1 : 0 < B := by 
    rcases hB with ⟨hb1, hb2⟩
    linarith
  have hB2 : B < Real.pi := by 
    rcases hB with ⟨hb1, hb2⟩
    linarith
  have hC1 : 0 < C := by 
    rcases hC with ⟨hc1, hc2⟩
    linarith
  have hC2 : C < Real.pi := by 
    rcases hC with ⟨hc1, hc2⟩
    linarith
  have h8 : C = Real.pi - (A + B) := by linarith [hABC]
  have h2 : cos C = -cos (A + B) := by 
    rw [show C = Real.pi - (A + B) by linarith [hABC]]
    rw [cos_pi_sub]
  have h3 : cos (A + B) = cos A * cos B - sin A * sin B := by 
    rw [cos_add]
  have h5 : sin A > 0 := by 
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith
  have h5₂ : sin B > 0 := by 
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith
  have h71 : (x - y * cos C - z * cos B) ^ 2 + (y * sin C - z * sin B) ^ 2 =
      x^2 + y^2 + z^2 - 2 * x * y * cos C - 2 * y * z * cos A - 2 * z * x * cos B := by
    have h13 : cos C = -cos (A + B) := h2
    have h14 : cos (A + B) = cos A * cos B - sin A * sin B := h3
    have h15 : cos C = - (cos A * cos B - sin A * sin B) := by
      rw [h13, h14]
    have h36 : sin C = sin (A + B) := by
      have h4 : C = Real.pi - (A + B) := h8
      rw [h4]
      rw [sin_pi_sub]
    have h37 : sin (A + B) = sin A * cos B + cos A * sin B := by
      rw [sin_add]
    have h38 : sin C = sin A * cos B + cos A * sin B := by
      rw [h36, h37]
    have eq2 : (x - y * cos C - z * cos B) ^ 2 + (y * sin C - z * sin B) ^ 2 =
        x^2 + y^2 + z^2 - 2 * x * y * cos C - 2 * y * z * cos A - 2 * z * x * cos B := by
      have eq3 : cos C = - (cos A * cos B - sin A * sin B) := h15
      have eq6 : sin C = sin A * cos B + cos A * sin B := h38
      simp only [eq3, eq6]
      ring_nf 
      <;> simp [Real.sin_sq, Real.cos_sq]
      <;> nlinarith [Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, Real.sin_sq_add_cos_sq (A + B), sq_nonneg (x * (sin A * sin B)), sq_nonneg (y * (sin A * sin B)), sq_nonneg (z * (sin A * sin B)), sq_nonneg (y - z), sq_nonneg (x - y * (cos A) - z * (cos B)), sq_nonneg (y * (sin A) - z * (sin B))]
    linarith
  have h7 : (x - y * cos C - z * cos B) ^ 2 + (y * sin C - z * sin B) ^ 2 ≥ 0 := by 
    positivity
  nlinarith [Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, Real.sin_sq_add_cos_sq C, sq_nonneg (y * (sin A) - z * (sin B)), sq_nonneg (x - y * cos C - z * cos B), sq_nonneg (y * sin C - z * sin B)]