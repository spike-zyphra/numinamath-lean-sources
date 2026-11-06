import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_312778 :
  IsLeast {x : ℝ | ∃ a b : ℝ, a > 0 ∧ b > 0 ∧ a * b = 1 ∧ x = 1 / (1 + a) + 1 / (1 + 2 * b)} (2 * sqrt 2 - 2) := by 
  constructor
  · -- Show that 2 * sqrt(2) - 2 belongs to the set
    use Real.sqrt 2, Real.sqrt 2 / 2
    constructor
    · -- Show a > 0
      positivity
    constructor
    · -- Show b > 0
      positivity
    constructor
    · -- Show a * b = 1
      have h1 : Real.sqrt 2 > 0 := by
        positivity
      have h2 : Real.sqrt 2 * (Real.sqrt 2 / 2) = 1 := by
        have h3 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by linarith)
        field_simp [h3]
        <;> ring_nf <;> nlinarith
      linarith [h2]
    · -- Show x = 2 * sqrt(2) - 2
      have eq1 : Real.sqrt 2 > 0 := by
        positivity
      have eq2 : (1 / (1 + Real.sqrt 2) + 1 / (1 + 2 * (Real.sqrt 2 / 2))) = 2 * Real.sqrt 2 - 2 := by
        have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by linarith)
        field_simp [(show 1 + Real.sqrt 2 ≠ 0 by positivity), (show 1 + Real.sqrt 2 ≠ 0 by positivity), 
          h1, (show Real.sqrt 2 > 0 by positivity)]
        <;> ring_nf 
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      linarith [eq2]
  · -- Show that 2 * sqrt(2) - 2 is the minimum
    intro x hx
    rcases hx with ⟨a, b, ha, hb, hab, hx⟩
    have h1 : b = 1 / a := by
      field_simp
      nlinarith [hab]
    have h2 : x = 1 / (1 + a) + 1 / (1 + 2 * (1 / a)) := by 
      rw [hx, h1]
    have h3 : x = (a + 2 + a * (1 + a)) / ((1 + a) * (a + 2)) := by 
      rw [h2]
      have denom_ne_zero : a + 1 ≠ 0 := by nlinarith
      have denom2_ne_zero : a + 2 ≠ 0 := by nlinarith
      field_simp [show a ≠ 0 by nlinarith, denom_ne_zero, show 1 + 2 * (1 / a) ≠ 0 by
        by_contra h
        field_simp [show a ≠ 0 by nlinarith] at h
        <;> nlinarith
      ]
      <;> ring
    have h4 : x = (a ^ 2 + 2 * a + 2) / ((a + 1) * (a + 2)) := by
      have h5 : x = (a + 2 + a * (1 + a)) / ((1 + a) * (a + 2)) := h3
      rw [h5]
      field_simp [show (1 + a) * (a + 2) ≠ 0 by positivity]
      <;> ring_nf
    have h7 : x ≥ 2 * Real.sqrt 2 - 2 := by 
      rw [h4]
      have h8 : (a ^ 2 + 2 * a + 2) ≥ (2 * Real.sqrt 2 - 2) * (a ^ 2 + 3 * a + 2) := by 
        nlinarith [sq_nonneg (a - Real.sqrt 2), sq_nonneg (a + 3 / 0 - Real.sqrt 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), 
          sq_nonneg (a + 1 / 0 - Real.sqrt 2 / 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (a * Real.sqrt 2 - 1), Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num)
        ]
      have h9 : (a ^ 2 + 2 * a + 2) / ((a + 1) * (a + 2)) ≥ 2 * Real.sqrt 2 - 2 := by 
        have h10 : (a + 1) * (a + 2) > 0 := by 
          positivity
        have h11 : (a ^ 2 + 2 * a + 2) ≥ (2 * Real.sqrt 2 - 2) * (a ^ 2 + 3 * a + 2) := h8 
        have h12 : (a ^ 2 + 2 * a + 2) / ((a + 1) * (a + 2)) ≥ 2 * Real.sqrt 2 - 2 := by 
          apply (le_div_iff₀ h10).mpr 
          nlinarith [h11]
        linarith 
      linarith
    linarith [h7]