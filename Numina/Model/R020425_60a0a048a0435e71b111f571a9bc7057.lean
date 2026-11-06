import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_160815 {f : ℝ → ℝ}
  (hf : f = λ x => (sqrt (x - 4 * sqrt (x - 4)) + 2) / (sqrt (x + 4 * sqrt (x - 4)) - 2)) :
  ∀ x, x ∈ Ioo 4 8 → f x = 4 / sqrt (x - 4) - 1 ∧
  ∀ x, x ∈ Ici 8 → f x = 1 := by
  intro x hx1
  rcases hx1 with ⟨hx3, hx4⟩
  have h1 : sqrt (x - 4 * sqrt (x - 4)) = 2 - Real.sqrt (x - 4) := by
    have h2 : x - 4 * Real.sqrt (x - 4) = (2 - Real.sqrt (x - 4)) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (x - 4), Real.sq_sqrt (show 0 ≤ (x - 4 : ℝ) by linarith)]
    rw [h2]
    have h3 : 2 - Real.sqrt (x - 4) ≥ 0 := by 
      nlinarith [Real.sqrt_nonneg (x - 4), Real.sq_sqrt (show 0 ≤ (x - 4 : ℝ) by linarith), show Real.sqrt (x - 4) < (2 : ℝ) by 
        nlinarith [Real.sqrt_nonneg (x - 4), Real.sq_sqrt (show 0 ≤ (x - 4 : ℝ) by linarith), hx4]
      ]
    rw [Real.sqrt_sq (h3)]
  have h4 : sqrt (x + 4 * Real.sqrt (x - 4)) = Real.sqrt (x - 4) + 2 := by
    have h5 : x + 4 * Real.sqrt (x - 4) = (Real.sqrt (x - 4) + 2) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (x - 4), Real.sq_sqrt (show 0 ≤ (x - 4 : ℝ) by linarith)]
    rw [h5]
    have h6 : 0 ≤ Real.sqrt (x - 4) + 2 := by
      linarith [Real.sqrt_nonneg (x - 4)]
    rw [Real.sqrt_sq (h6)]
  have h5 : f x = (sqrt (x - 4 * sqrt (x - 4)) + 2) / (sqrt (x + 4 * sqrt (x - 4)) - 2) := by 
    rw [hf]
  have h6 : Real.sqrt (x - 4) > 0 := by 
    apply Real.sqrt_pos.mpr 
    linarith
  have h7 : ( (2 - Real.sqrt (x - 4)) + 2 ) / ( (Real.sqrt (x - 4) + 2) - 2 ) = 4 / Real.sqrt (x - 4) - 1 := by
    have h8 : Real.sqrt (x - 4) > 0 := h6 
    field_simp [h8]
    <;> nlinarith [Real.sqrt_nonneg (x - 4), Real.sq_sqrt (show 0 ≤ (x - 4 : ℝ) by linarith)]
  constructor
  · -- First part
    rw [h5]
    rw [h1, h4]
    linarith [h7]
  · -- Second part
    intro y hy 
    have h1y : 8 ≤ y := by 
      have h1y' : y ∈ Ici 8 := hy 
      simpa using h1y'
    have h12y : sqrt (y - 4 * sqrt (y - 4)) = Real.sqrt (y - 4) - 2 := by
      have h2y : y - 4 * Real.sqrt (y - 4) = (Real.sqrt (y - 4) - 2) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (y - 4), Real.sq_sqrt (show 0 ≤ (y - 4 : ℝ) by linarith), show Real.sqrt (y - 4) ≥ (2 : ℝ) by 
          nlinarith [Real.sqrt_nonneg (y - 4), Real.sq_sqrt (show 0 ≤ (y - 4 : ℝ) by linarith), h1y]
        ]
      rw [h2y]
      have h3y : 0 ≤ Real.sqrt (y - 4) - 2 := by 
        nlinarith [Real.sqrt_nonneg (y - 4), Real.sq_sqrt (show 0 ≤ (y - 4 : ℝ) by linarith), h1y]
      rw [Real.sqrt_sq (h3y)]
    have h13y : sqrt (y + 4 * Real.sqrt (y - 4)) = Real.sqrt (y - 4) + 2 := by
      have h5y : y + 4 * Real.sqrt (y - 4) = (Real.sqrt (y - 4) + 2) ^ 2 := by 
        nlinarith [Real.sqrt_nonneg (y - 4), Real.sq_sqrt (show 0 ≤ (y - 4 : ℝ) by linarith)]
      rw [h5y]
      have h6y : 0 ≤ Real.sqrt (y - 4) + 2 := by 
        linarith [Real.sqrt_nonneg (y - 4)]
      rw [Real.sqrt_sq (h6y)]
    have h5y : f y = (sqrt (y - 4 * sqrt (y - 4)) + 2) / (sqrt (y + 4 * sqrt (y - 4)) - 2) := by 
      rw [hf]
    rw [h5y]
    rw [h12y, h13y]
    have h11y : Real.sqrt (y - 4) > 0 := by
      apply Real.sqrt_pos.mpr 
      linarith
    field_simp [show Real.sqrt (y - 4) + 2 - 2 ≠ 0 by 
      have h15y : Real.sqrt (y - 4) > 0 := h11y 
      nlinarith [Real.sqrt_nonneg (y - 4)]
    ]
    <;> nlinarith [Real.sqrt_nonneg (y - 4), Real.sq_sqrt (show 0 ≤ (y - 4 : ℝ) by linarith)]