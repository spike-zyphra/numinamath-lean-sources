import Mathlib

theorem algebra_128642 (a b c : ℝ) (ha : a ≠ 0) (h : a + b + c < 0)
    (h1 : ∀ x : ℝ, a * x ^ 2 + b * x + c ≠ 0) : c < 0 := by
  by_contra h2
  push_neg at h2
  have h3 : a + b < 0 := by linarith 
  have h4 : c ≠ 0 := by 
    by_contra h5
    have h5' : c = 0 := by linarith
    specialize h1 0
    simp [h5'] at h1
  have h5 : c > 0 := by
    by_contra h6 
    push_neg at h6 
    have h7 : c ≤ 0 := by linarith
    have h8 : c = 0 := by 
      have h8 : c ≤ 0 := by linarith
      have h9 : c ≥ 0 := by linarith
      linarith
    contradiction
  have h6 : (b) ^ 2 - 4 * a * c < 0 := by 
    by_contra h7
    push_neg at h7
    have h8 : ∃ x : ℝ, a * x ^ 2 + b * x + c = 0 := by
      have h9 : (b) ^ 2 - 4 * a * c ≥ 0 := by linarith
      have h10 : a ≠ 0 := ha
      use (-b + Real.sqrt ((b) ^ 2 - 4 * a * c)) / (2 * a)
      field_simp [ha]
      ring_nf
      rw [Real.sq_sqrt (by nlinarith)]
      <;> nlinarith
    rcases h8 with ⟨x, hx⟩ 
    have h9 : a * x ^ 2 + b * x + c = 0 := hx
    have h9' := h1 x 
    contradiction 
  have h7 : a < 0 := by 
    nlinarith [sq_nonneg (b), sq_nonneg (a), sq_nonneg (b + 2 * a), sq_nonneg ((-b) + 2 * a), h5, h6]
  nlinarith [sq_nonneg (b + a), sq_nonneg (b - c), sq_nonneg (b + 2 * a), sq_nonneg ((-b) + 2 * a), sq_nonneg ((b) ^ 2 - 4 * a * c), sq_pos_of_neg (show a < 0 by linarith), h5, h6, h7]