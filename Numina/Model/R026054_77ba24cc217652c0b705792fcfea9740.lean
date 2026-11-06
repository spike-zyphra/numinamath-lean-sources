import Mathlib

theorem algebra_213098 {C U ε Q : ℝ} (hC : C > 0) (hU : U > 0) (hε : ε > 0)
    (hQ : Q > 0) (h1 : (C * U ^ 2) / (2 * ε) + (C * U ^ 2) / 2 = (C * U ^ 2) / 2 * (ε + 1) / ε)
    (h2 : (2 * C * U ^ 2 * ε) / (ε + 1) ^ 2 + (2 * C * U ^ 2) / (ε + 1) ^ 2 = (2 * C * U ^ 2) / (ε + 1))
    (h3 : Q = (C * U ^ 2 * (ε - 1) ^ 2) / (2 * ε * (ε + 1))) :
    C = (2 * ε * (ε + 1) * Q) / (U ^ 2 * (ε - 1) ^ 2) := by
  have h5 : (ε - 1) ^ 2 > 0 := by
    by_contra h
    push_neg at h 
    have h6 : (ε - 1) ^ 2 = 0 := by
      nlinarith [show (ε - 1) ^ 2 ≥ 0 by positivity, h]
    have h7 : ε - 1 = 0 := by
      nlinarith
    have h8 : ε = 1 := by
      nlinarith
    rw [h8] at h3 
    field_simp at h3 
    nlinarith
  have h6 : (U ^ 2 * (ε - 1) ^ 2) > 0 := by
    have h7 : U ^ 2 > 0 := by nlinarith 
    have h8 : (ε - 1) ^ 2 > 0 := h5 
    positivity
  have h4 : (C * U ^ 2 * (ε - 1) ^ 2) = (2 * ε * (ε + 1) * Q) := by
    have h5 : (ε * (ε + 1)) > 0 := by
      apply mul_pos 
      linarith
      nlinarith
    have h7 : Q = (C * U ^ 2 * (ε - 1) ^ 2) / (2 * ε * (ε + 1)) := h3 
    have h8 : (2 * ε * (ε + 1)) > 0 := by
      positivity 
    field_simp [show ε > 0 by linarith, show ε + 1 > 0 by nlinarith, h5] at h7 ⊢ 
    nlinarith 
  have h7 : C = (2 * ε * (ε + 1) * Q) / (U ^ 2 * (ε - 1) ^ 2) := by
    have h9 : (C * U ^ 2 * (ε - 1) ^ 2) = (2 * ε * (ε + 1) * Q) := h4
    have h10 : (U ^ 2 * (ε - 1) ^ 2) > 0 := h6
    field_simp [h10] at h9 ⊢ 
    <;> nlinarith 
  exact h7