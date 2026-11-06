import Mathlib

open Real Set

theorem algebra_15129 :
    IsLeast {t : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x + y + z = 6 ∧ t = (x ^ 2 + y ^ 2) / (x + y) +
      (x ^ 2 + z ^ 2) / (x + z) + (y ^ 2 + z ^ 2) / (y + z)} 6 := by
  constructor
  · -- Show that (2, 2, 2) achieves 6
    use 2, 2, 2
    norm_num
  · -- Show that 6 is a lower bound
    rintro t ⟨x, y, z, hx, hy, hz, hxyz, ht⟩
    have h1 : (x ^ 2 + y ^ 2) / (x + y) ≥ (x + y) / 2 := by 
      have h4 : x + y > 0 := by linarith
      have h5 : x ^ 2 + y ^ 2 ≥ (x + y) * ((x + y) / 2) := by
        nlinarith [sq_nonneg (x - y)]
      have h7 : (x ^ 2 + y ^ 2) / (x + y) ≥ (x + y) / 2 := by
        apply (le_div_iff₀' h4).mpr 
        nlinarith 
      linarith
    have h2 : (x ^ 2 + z ^ 2) / (x + z) ≥ (x + z) / 2 := by
      have h5 : x + z > 0 := by linarith
      have h6 : x ^ 2 + z ^ 2 ≥ (x + z) * ((x + z) / 2) := by
        nlinarith [sq_nonneg (x - z)]
      have h7 : (x ^ 2 + z ^ 2) / (x + z) ≥ (x + z) / 2 := by
        apply (le_div_iff₀' h5).mpr 
        nlinarith 
      linarith
    have h3 : (y ^ 2 + z ^ 2) / (y + z) ≥ (y + z) / 2 := by
      have h5 : y + z > 0 := by linarith
      have h6 : y ^ 2 + z ^ 2 ≥ (y + z) * ((y + z) / 2) := by
        nlinarith [sq_nonneg (y - z)]
      have h7 : (y ^ 2 + z ^ 2) / (y + z) ≥ (y + z) / 2 := by
        apply (le_div_iff₀' h5).mpr 
        nlinarith 
      linarith
    have h5 : (x ^ 2 + y ^ 2) / (x + y) + (x ^ 2 + z ^ 2) / (x + z) + (y ^ 2 + z ^ 2) / (y + z) ≥ (x + y) / 2 + (x + z) / 2 + (y + z) / 2 := by linarith [h1, h2, h3]
    have h6 : (x ^ 2 + y ^ 2) / (x + y) + (x ^ 2 + z ^ 2) / (x + z) + (y ^ 2 + z ^ 2) / (y + z) ≥ 6 := by
      linarith [h5, hxyz]
    linarith [ht, h6]