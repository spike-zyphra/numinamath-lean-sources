import Mathlib

theorem algebra_454 {x : ℝ} (hx : 2 * x ^ 2 + 5 * x - 3 ≠ 0 ∧ 2 * x - 1 ≠ 0) :
    (5 * x + 1) / (2 * x ^ 2 + 5 * x - 3) = 2 * x / (2 * x - 1) ↔ x = -1 := by
  constructor
  · -- Forward direction: equation implies x = -1
    intro h
    rcases hx with ⟨hx1, hx2⟩
    have h1 : (5 * x + 1) / (2 * x ^ 2 + 5 * x - 3) = 2 * x / (2 * x - 1) := h
    have h2 : (5 * x + 1) * (2 * x - 1) = 2 * x * (2 * x ^ 2 + 5 * x - 3) := by
      field_simp [(show 2 * x ^ 2 + 5 * x - 3 ≠ 0 by exact hx1), (show 2 * x - 1 ≠ 0 by exact hx2)] at h1 ⊢
      linarith
    have h3 : 4 * x ^ 3 - 3 * x + 1 = 0 := by
      ring_nf at h2 ⊢
      linarith
    have h4 : (x + 1) * (2 * x - 1) ^ 2 = 0 := by 
      ring_nf at h3 ⊢
      linarith 
    cases' (mul_eq_zero.mp h4) with h5 h6 
    · -- Case where x + 1 = 0, so x = -1 
      linarith 
    · -- Case where (2x - 1)^2 = 0, so 2x - 1 = 0, and x = 1/2, but this contradicts the assumption that 2x - 1 ≠ 0 
      have h7 : 2 * x - 1 = 0 := by 
        apply pow_eq_zero 
        exact h6 
      contradiction 
  · -- Backward direction: x = -1 implies the equation 
    intro h 
    rw [h] 
    norm_num