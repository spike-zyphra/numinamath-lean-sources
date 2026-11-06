import Mathlib

open Real

namespace Inequalities_605588

open Real

theorem Inequalities_605588 (x y z : ℝ) (h : 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z) (nz : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) :
  (2 * x^2 - x + y + z) / (x + y^2 + z^2) +
  (2 * y^2 + x - y + z) / (x^2 + y + z^2) +
  (2 * z^2 + x + y - z) / (x^2 + y^2 + z) ≥ 3 := by 
  rcases h with ⟨hx, hy, hz⟩
  have pos1 : x + y^2 + z^2 > 0 := by
    by_contra h1
    push_neg at h1
    have h2 : x ≤ 0 := by nlinarith [h1, sq_nonneg (y), sq_nonneg (z)]
    have h3 : x = 0 := by linarith [h2, hx]
    have h4 : y^2 + z^2 = 0 := by nlinarith [h1, h3]
    have h5 : y = 0 := by nlinarith [h4, sq_nonneg (y), sq_nonneg (z)]
    have h6 : z = 0 := by nlinarith [h4, sq_nonneg (y), sq_nonneg (z)]
    rcases nz with (h1 | h2 | h3)
    · contradiction
    · contradiction
    · contradiction
  have pos2 : x^2 + y + z^2 > 0 := by
    by_contra h2
    push_neg at h2
    have h4 : y ≤ 0 := by nlinarith [h2, sq_nonneg (x), sq_nonneg (z)]
    have h5 : y = 0 := by nlinarith [h4, sq_nonneg (x), sq_nonneg (z)]
    have h7 : x^2 + z^2 = 0 := by nlinarith [h2, h5]
    have hx' : x = 0 := by nlinarith [h7, sq_nonneg (x), sq_nonneg (z)]
    have hz' : z = 0 := by nlinarith [h7, sq_nonneg (x), sq_nonneg (z)]
    rcases nz with (h1 | h2 | h3)
    · contradiction
    · contradiction
    · contradiction
  have pos3 : x^2 + y^2 + z > 0 := by
    by_contra h3
    push_neg at h3
    have h4 : z ≤ 0 := by nlinarith [h3, sq_nonneg (x), sq_nonneg (y)]
    have h5 : z = 0 := by nlinarith [h4, sq_nonneg (x), sq_nonneg (y)]
    have h7 : x^2 + y^2 = 0 := by nlinarith [h3, h5]
    have hx' : x = 0 := by nlinarith [h7, sq_nonneg (x), sq_nonneg (y)]
    have h6 : y = 0 := by nlinarith [h7, sq_nonneg (x), sq_nonneg (y)]
    rcases nz with (h1 | h2 | h3)
    · contradiction
    · contradiction
    · contradiction

  have h1 : (2 * x^2 - x + y + z) / (x + y^2 + z^2) + (2 * y^2 + x - y + z) / (x^2 + y + z^2) + (2 * z^2 + x + y - z) / (x^2 + y^2 + z) - 3 ≥ 0 := by
    have pos1' : x + y^2 + z^2 > 0 := pos1
    have pos2' : x^2 + y + z^2 > 0 := pos2
    have pos3' : x^2 + y^2 + z > 0 := pos3
    have h' : (2 * x^2 - x + y + z) / (x + y^2 + z^2) + (2 * y^2 + x - y + z) / (x^2 + y + z^2) + (2 * z^2 + x + y - z) / (x^2 + y^2 + z) - 3 =
      ((2 * x^2 - x + y + z) * (x^2 + y + z^2) * (x^2 + y^2 + z) + (2 * y^2 + x - y + z) * (x + y^2 + z^2) * (x^2 + y^2 + z) + (2 * z^2 + x + y - z) * (x + y^2 + z^2) * (x^2 + y + z^2) - 3 * (x + y^2 + z^2) * (x^2 + y + z^2) * (x^2 + y^2 + z)) / ((x + y^2 + z^2) * (x^2 + y + z^2) * (x^2 + y^2 + z)) := by
      field_simp [pos1', pos2', pos3']
      ring
    rw [h']
    apply div_nonneg
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (2 * x^2 - x + y + z - (x + y^2 + z^2)), 
      sq_nonneg (2 * y^2 + x - y + z - (x^2 + y + z^2)), 
      sq_nonneg (2 * z^2 + x + y - z - (x^2 + y^2 + z)), 
      mul_pos (show 0 < x + y^2 + z^2 by linarith [pos1]) (show 0 < x^2 + y + z^2 by linarith [pos2]), 
      mul_pos (show 0 < x^2 + y + z^2 by linarith [pos2]) (show 0 < x^2 + y^2 + z by linarith [pos3]), 
      mul_pos (show 0 < x + y^2 + z^2 by linarith [pos1]) (show 0 < x^2 + y^2 + z by linarith [pos3])
      ]
    positivity
  linarith [h1]