import Mathlib

theorem algebra_216718 {x y z : ℤ} (h1 : x - y * z = 1) (h2 : x * z + y = 2) :
    (x = 1 ∧ y = 0 ∧ z = 2) ∨ (x = 1 ∧ y = 2 ∧ z = 0) := by 
  have h3 : x = 1 + y * z := by 
    linarith 
  have h4 : y * (z ^ 2 + 1) = 2 - z := by 
    rw [h3] at h2
    ring_nf at h2 ⊢ 
    linarith 
  have h5 : z = 0 ∨ z = 2 := by 
    have h6 : y * (z ^ 2 + 1) = 2 - z := h4
    have h7 : z ≤ 2 := by
      by_contra h8 
      push_neg at h8 
      have h8' : z ≥ 3 := by linarith 
      have h9 : y = 0 := by 
        nlinarith [sq_nonneg (z * y), sq_nonneg (z - 2), sq_nonneg (y), sq_nonneg (z ^ 2 - 1), sq_nonneg (y * z), sq_nonneg (z), sq_nonneg (y - 0), sq_nonneg (z - 2)]
      rw [h9] at h6
      nlinarith 
    have h8 : z ≥ -2 := by 
      by_contra h9 
      push_neg at h9 
      have h9' : z ≤ -3 := by linarith 
      have h9 : y = 0 := by 
        nlinarith [sq_nonneg (z * y), sq_nonneg (z + 2), sq_nonneg (y), sq_nonneg (z ^ 2 - 1), sq_nonneg (y * z), sq_nonneg (z), sq_nonneg (y - 0), sq_nonneg (z + 2)]
      rw [h9] at h6 
      nlinarith
    have : z = 0 ∨ z = 2 := by
      interval_cases z <;> omega 
    assumption 
  cases h5 with 
  | inl hz0 => 
    have h9 : z = 0 := hz0 
    have h10 : y = 2 := by 
      rw [h9] at h4 
      nlinarith 
    have h11 : x = 1 := by 
      rw [h10, h9] at h3 
      linarith 
    right 
    constructor 
    · exact h11 
    constructor 
    · exact h10 
    · exact h9 
  | inr hz2 => 
    have h12 : z = 2 := hz2 
    have h13 : y = 0 := by 
      rw [h12] at h4 
      nlinarith 
    have h14 : x = 1 := by 
      rw [h13, h12] at h3 
      linarith 
    left 
    constructor 
    · exact h14 
    constructor 
    · exact h13 
    · exact h12