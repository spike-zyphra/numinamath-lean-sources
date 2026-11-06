import Mathlib

theorem algebra_14102 (x : ℝ) (hx : x ≠ 1) :
    (2 * x + 4) / (x ^ 2 + 4 * x - 5) = (2 - x) / (x - 1) ↔ x = -6 := by
  constructor
  · -- Forward direction: if \(\frac{2x+4}{x^2+4x-5}=\frac{2-x}{x-1}\), then \(x = -6\)
    intro h
    have h1 : x ^ 2 + 4 * x - 5 ≠ 0 := by
      by_contra h2
      have : (x - 1) * (x + 5) = 0 := by
        linarith 
      cases' (mul_eq_zero.1 this) with h3 h4
      · -- x - 1 = 0, so x = 1 contradicts hx : x ≠ 1
        have : x = 1 := by linarith
        tauto 
      · -- x + 5 = 0, so x = -5 
        have : x = -5 := by linarith 
        rw [this] at h 
        norm_num at h 
    have hx2 : x - 1 ≠ 0 := by
      intro h
      apply hx
      linarith 
    have h3 : (2 * x + 4) * (x - 1) = (2 - x) * (x ^ 2 + 4 * x - 5) := by 
      have denom1 : x ^ 2 + 4 * x - 5 ≠ 0 := h1 
      have denom2 : x - 1 ≠ 0 := hx2 
      field_simp [denom1, denom2] at h ⊢ 
      linarith 
    have h4 : (x + 6) * (x - 1)^2 = 0 := by 
      nlinarith [sq_pos_of_ne_zero (show (x - 1) ≠ 0 by exact hx2), sq_nonneg (x + 6), sq_nonneg (x - 1)]
    cases' (mul_eq_zero.1 h4) with h5 h6
    · -- \(x +6 =0\), so \(x = -6\) which is the desired solution.
      have : x = -6 := by linarith 
      tauto 
    · -- \( (x -1)^2 =0 \), so \(x =1 \), which is excluded.
      have h7 : x = 1 := by 
        nlinarith 
      tauto 
  · -- Backward direction: if \(x = -6\), then \(\frac{2x+4}{x^2+4x-5}=\frac{2-x}{x-1}\)
    intro h
    rw [h]
    norm_num