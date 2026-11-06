import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_598144 :
  IsLeast {t : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x^2 + y^2 + z^2 = 1 ∧ t = x / (1 - x^2) + y / (1 - y^2) + z / (1 - z^2)} (3 * sqrt 3 / 2) := by
  constructor
  · -- Show that 3 * sqrt(3) / 2 is in the set
    use Real.sqrt 3 / 3, Real.sqrt 3 / 3, Real.sqrt 3 / 3 
    constructor 
    · -- Show x > 0 
      have h1 : Real.sqrt 3 > 0 := by 
        apply Real.sqrt_pos.mpr 
        linarith 
      nlinarith 
    constructor 
    · -- Show y > 0 
      have h1 : Real.sqrt 3 > 0 := by 
        apply Real.sqrt_pos.mpr 
        linarith 
      nlinarith 
    constructor 
    · -- Show z > 0 
      have h1 : Real.sqrt 3 > 0 := by 
        apply Real.sqrt_pos.mpr 
        linarith 
      nlinarith 
    constructor
    · -- Show x^2 + y^2 + z^2 = 1 
      have h1 : (Real.sqrt 3 / 3 : ℝ) ^ 2 = 1 / 3 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      nlinarith 
    · -- Show t = x / (1 - x^2) + y / (1 - y^2) + z / (1 - z^2)
      have h2 : (Real.sqrt 3 / 3 : ℝ) ^ 2 = 1 / 3 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have eq1 : (Real.sqrt 3 / 3 : ℝ) / (1 - (Real.sqrt 3 / 3 : ℝ) ^ 2) = Real.sqrt 3 / 2 := by 
        rw [show (Real.sqrt 3 / 3 : ℝ) ^ 2 = 1 / 3 by linarith [h2]]
        field_simp 
        <;> nlinarith 
      have eq2 : (Real.sqrt 3 / 3 : ℝ) / (1 - (Real.sqrt 3 / 3 : ℝ) ^ 2) + (Real.sqrt 3 / 3 : ℝ) / (1 - (Real.sqrt 3 / 3 : ℝ) ^ 2) + (Real.sqrt 3 / 3 : ℝ) / (1 - (Real.sqrt 3 / 3 : ℝ) ^ 2) = 3 * Real.sqrt 3 / 2 := by
        rw [eq1] 
        ring 
      linarith [eq2]
  · -- Show that 3 * sqrt(3) / 2 is a lower bound
    intro t ht 
    rcases ht with ⟨x, y, z, hx, hy, hz, h1, ht⟩ 
    have h2 : x / (1 - x^2) ≥ (3 * Real.sqrt 3 / 2) * x^2 := by
      have hx1 : 0 < x := hx
      have hx2 : x < 1 := by nlinarith [h1, sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz]
      have h211 : 0 < 1 - x^2 := by nlinarith 
      have h311 : x / (1 - x^2) ≥ (3 * Real.sqrt 3 / 2) * x^2 := by 
        apply (le_div_iff₀ (by linarith)).mpr 
        nlinarith [sq_nonneg (x^2 - 1/3), sq_nonneg (x - Real.sqrt 3 / 3), Real.sqrt_nonneg 3, 
          Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith), 
          mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3),
          sq_nonneg (x^2 - 1/3), sq_nonneg (x - Real.sqrt 3 / 3), 
          mul_pos hx (show 0 < 1 - x^2 by nlinarith)]
      exact h311 
    have h3 : y / (1 - y^2) ≥ (3 * Real.sqrt 3 / 2) * y^2 := by
      have hy1 : 0 < y := hy
      have hy2 : y < 1 := by nlinarith [h1, sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz]
      have h211 : 0 < 1 - y^2 := by nlinarith 
      have h311 : y / (1 - y^2) ≥ (3 * Real.sqrt 3 / 2) * y^2 := by 
        apply (le_div_iff₀ (by linarith)).mpr 
        nlinarith [sq_nonneg (y^2 - 1/3), sq_nonneg (y - Real.sqrt 3 / 3), Real.sqrt_nonneg 3, 
          Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith), 
          mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3),
          sq_nonneg (y^2 - 1/3), sq_nonneg (y - Real.sqrt 3 / 3), 
          mul_pos hy (show 0 < 1 - y^2 by nlinarith)]
      exact h311
    have h4 : z / (1 - z^2) ≥ (3 * Real.sqrt 3 / 2) * z^2 := by
      have hz1 : 0 < z := hz
      have hz2 : z < 1 := by nlinarith [h1, sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz]
      have h211 : 0 < 1 - z^2 := by nlinarith 
      have h311 : z / (1 - z^2) ≥ (3 * Real.sqrt 3 / 2) * z^2 := by 
        apply (le_div_iff₀ ( by linarith)).mpr 
        nlinarith [sq_nonneg (z^2 - 1/3), sq_nonneg (z - Real.sqrt 3 / 3), Real.sqrt_nonneg 3, 
          Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith), 
          mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3),
          sq_nonneg (z^2 - 1/3), sq_nonneg (z - Real.sqrt 3 / 3), 
          mul_pos hz (show 0 < 1 - z^2 by nlinarith)]
      exact h311
    have h5 : x / (1 - x^2) + y / (1 - y^2) + z / (1 - z^2) ≥ 3 * Real.sqrt 3 / 2 := by 
      have h6 : x^2 + y^2 + z^2 = 1 := h1 
      nlinarith [h2, h3, h4, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3)]
    linarith [ht, h5]