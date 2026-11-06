import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_319244 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
  (h : x^2 + y^2 + z^2 = 1) :
  IsLeast {t | ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x^2 + y^2 + z^2 = 1 ∧ t = 1/x^2 + 1/y^2 + 1/z^2} 9 := by
  constructor
  · -- Show that 9 is achievable, using x = y = z = sqrt(3)/3
    use Real.sqrt 3 / 3, Real.sqrt 3 / 3, Real.sqrt 3 / 3
    constructor
    · -- Show x > 0
      have h1 : 0 < Real.sqrt 3 / 3 := by
        have h2 : 0 < (Real.sqrt 3 : ℝ) := by
          positivity
        linarith
      linarith
    constructor
    · -- Show y > 0
      have h1 : 0 < Real.sqrt 3 / 3 := by
        have h2 : 0 < (Real.sqrt 3 : ℝ) := by
          positivity
        linarith
      linarith
    constructor
    · -- Show z > 0
      have h1 : 0 < Real.sqrt 3 / 3 := by
        have h2 : 0 < (Real.sqrt 3 : ℝ) := by
          positivity
        linarith
      linarith
    constructor
    · -- Show x^2 + y^2 + z^2 = 1
      have h1 : (Real.sqrt 3 / 3 : ℝ) ^ 2 = (1 / 3 : ℝ) := by
        calc
          (Real.sqrt 3 / 3 : ℝ) ^ 2 = (Real.sqrt 3) ^ 2 / 9 := by ring_nf
          _ = 3 / 9 := by rw [Real.sq_sqrt]; all_goals linarith
          _ = (1 / 3 : ℝ) := by norm_num
      linarith [h1]
    · -- Show 9 = 1/x^2 + 1/y^2 + 1/z^2
      have h1 : (Real.sqrt 3 / 3 : ℝ) ^ 2 = (1 / 3 : ℝ) := by
        calc
          (Real.sqrt 3 / 3 : ℝ) ^ 2 = (Real.sqrt 3) ^ 2 / 9 := by ring_nf
          _ = 3 / 9 := by rw [Real.sq_sqrt]; all_goals linarith
          _ = (1 / 3 : ℝ) := by norm_num
      rw [show 1 / (Real.sqrt 3 / 3 : ℝ) ^ 2 = 3 by
          rw [h1]
          field_simp
          <;> norm_num
      ]
      all_goals norm_num
  · -- Show that 9 is the least in the set.
    intro t ht
    rcases ht with ⟨x, y, z, hx, hy, hz, h1, ht⟩
    have h2 : 1 / x^2 + 1 / y^2 + 1 / z^2 ≥ 9 := by
      have hx2_pos : 0 < x^2 := by positivity
      have hy2_pos : 0 < y^2 := by positivity
      have hz2_pos : 0 < z^2 := by positivity
      have h4 : x^2 + y^2 + z^2 = 1 := h1
      have h5 : (y^2 * z^2 + x^2 * z^2 + x^2 * y^2) ≥ 9 * x^2 * y^2 * z^2 := by
        nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (y^2 - z^2), sq_nonneg (z^2 - x^2), 
                  sq_nonneg (x * y * z), 
                  sq_nonneg (x^2 + y^2 + z^2 - 1), 
                  mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, 
                  mul_pos (show 0 < x^2 by positivity) (show 0 < y^2 by positivity), 
                  mul_pos (show 0 < x^2 by positivity) (show 0 < z^2 by positivity), 
                  mul_pos (show 0 < y^2 by positivity) (show 0 < z^2 by positivity), 
                  h1
              ]
      have hx2y2z2_pos : 0 < x^2 * y^2 * z^2 := by positivity
      have h7 : (1 / x^2 + 1 / y^2 + 1 / z^2 - 9) ≥ 0 := by
        have h8 : (1 / x^2 + 1 / y^2 + 1 / z^2 - 9) = (y^2 * z^2 + x^2 * z^2 + x^2 * y^2 - 9 * x^2 * y^2 * z^2) / (x^2 * y^2 * z^2) := by
          field_simp
          <;> ring
        rw [h8]
        apply div_nonneg 
        linarith
        positivity
      linarith
    linarith [ht, h2]