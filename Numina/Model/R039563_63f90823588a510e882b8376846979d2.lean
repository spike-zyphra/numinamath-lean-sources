import Mathlib

theorem algebra_170105 {b c : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 + b * x + c)
    (h : ¬∃ x, f x = x) :
    ¬∃ x, f (f x) = x := by 
  rintro ⟨x, hx⟩
  have h1 : f (f x) = x := hx
  have h5 : ∀ z, f z ≠ z := by
    intro z hz
    apply h
    exact ⟨z, hz⟩
  have h5' : f x ≠ x := by 
    apply h5 x
  have h3 : (f x) ^ 2 + b * (f x) + c = x := by
    have h1' : f (f x) = x := h1
    rw [hf] at h1'
    linarith
  have h4 : f x = x ^ 2 + b * x + c := by 
    rw [hf]
  have h9 : x ^ 2 + b * x + c ≠ x := by
    intro h10
    have h11 : f x = x := by
      linarith [h10, h4]
    contradiction
  have h10 : b ^ 2 - 2 * b + 1 < 4 * c := by
    by_contra h11
    push_neg at h11
    have h11' : ∃ z, f z = z := by
      have h12 : ( (1 - b) / 2 + Real.sqrt ( (b - 1) ^ 2 - 4 * c ) / 2 ) ^ 2 + b * ( (1 - b) / 2 + Real.sqrt ( (b - 1) ^ 2 - 4 * c ) / 2 ) + c = ( (1 - b) / 2 + Real.sqrt ( (b - 1) ^ 2 - 4 * c ) / 2 ) := by
        nlinarith [ Real.sqrt_nonneg ( (b - 1) ^ 2 - 4 * c ), Real.sq_sqrt (show ( (b - 1) ^ 2 - 4 * c ) ≥ 0 by nlinarith ) ]
      exact ⟨ ( (1 - b) / 2 + Real.sqrt ( (b - 1) ^ 2 - 4 * c ) / 2 ), by
        rw [hf]
        linarith
      ⟩
    contradiction
  rw [h4] at h3
  nlinarith [ sq_nonneg (x ^ 2 + b * x + c - x), sq_nonneg (x + (b - 1) / 2), sq_nonneg ((x ^ 2 + b * x + c) + (b - 1) / 2) ]