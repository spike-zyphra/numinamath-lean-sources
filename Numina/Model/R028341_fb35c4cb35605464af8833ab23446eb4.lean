import Mathlib

theorem algebra_18932 (k : ℝ) (hk : k ≠ 0):
  (∃ x : ℝ, k * x ^ 2 - 3 * k * x + 4 * k + 7 = 0) ↔ k ≥ -4 ∧ k < 0 := by
  constructor
  · -- Assume ∃ x : ℝ, k * x ^ 2 - 3 * k * x + 4 * k + 7 = 0, prove k ≥ -4 ∧ k < 0
    intro h
    rcases h with ⟨x, hx⟩
    
    have h1 : k < 0 := by
      by_contra h2
      push_neg at h2
      have h3 : x^2 - 3 * x + 4 > 0 := by
        nlinarith [sq_nonneg (x - 3 / 2)]
      have h4 : k * (x^2 - 3 * x + 4) ≥ 0 := by 
        apply mul_nonneg 
        linarith 
        nlinarith [sq_nonneg (x - 3 / 2)]
      have h5 : k * (x^2 - 3 * x + 4) = -7 := by 
        nlinarith [hx]
      linarith [h5, h4]
    
    have h2 : k ≥ -4 := by
      have h3 : (-3 * k : ℝ) ^ 2 - 4 * k * (4 * k + 7) ≥ 0 := by
        have hx2 : k * x ^ 2 - 3 * k * x + 4 * k + 7 = 0 := hx
        nlinarith [sq_nonneg (k * x - k * 3 / 2), sq_nonneg (x - 3 / 2), sq_nonneg (k * (x ^ 2 - 3 * x + 4)), sq_nonneg (k), sq_nonneg (x ^ 2 - 3 * x + 4), sq_pos_of_pos (show (0 : ℝ) < (x ^ 2 - 3 * x + 4) by nlinarith [sq_nonneg (x - 3 / 2)]) ]
      nlinarith [sq_nonneg (k + 4)]
    
    constructor
    · -- k ≥ -4
      linarith 
    · -- k < 0
      linarith
  
  · -- Assume k ≥ -4 ∧ k < 0, prove ∃ x : ℝ, k * x ^ 2 - 3 * k * x + 4 * k + 7 = 0
    rintro ⟨hk1, hk2⟩
    
    have h3 : (-3 * k : ℝ) ^ 2 - 4 * k * (4 * k + 7) ≥ 0 := by
      nlinarith [sq_nonneg (k + 4), sq_nonneg (k * (k + 4)), sq_nonneg (k * 2), sq_nonneg ((k + 4) * 2), sq_nonneg (k + 2), sq_nonneg (k * (k+4)), sq_nonneg ((k + 4) * k), sq_nonneg (k^2)]
    
    use (3 * k - Real.sqrt ((-3 * k) ^ 2 - 4 * k * (4 * k + 7))) / (2 * k)

    field_simp [(show k ≠ 0 by assumption)]
    <;> ring_nf <;> rw [Real.sq_sqrt (by nlinarith)] 
    <;> nlinarith [Real.sqrt_nonneg ((-3 * k) ^ 2 -4 * k * (4 * k + 7)), sq_nonneg (k + 4) ]