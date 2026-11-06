import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_20861 :
  IsLeast {x : ℝ | ∃ a b : ℝ, a > 0 ∧ b > 0 ∧ x = (a^2 + b^2)^2 / (a^3 * b)} (16 * sqrt 3 / 9) := by 
  constructor
  · -- Show that 16 * sqrt 3 / 9 is in the set.
    use Real.sqrt 3, (1 : ℝ)
    constructor
    · -- Show that sqrt 3 > 0.
      positivity
    constructor
    · -- Show that 1 > 0.
      norm_num
    · -- Show that x = (a^2 + b^2)^2 / (a^3 * b).
      have h1 : Real.sqrt 3 ^ 2 = 3 := by
        exact Real.sq_sqrt (by linarith)
      have h2 : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
        calc
          Real.sqrt 3 ^ 3 = (Real.sqrt 3) ^ 2 * Real.sqrt 3 := by ring
          _ = 3 * Real.sqrt 3 := by
            rw [h1]
      field_simp [h1, h2]
      <;> nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by linarith : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith)]
  · -- Show that 16 * sqrt 3 / 9 is the least.
    intro x hx
    rcases hx with ⟨a, b, ha, hb, h_eq⟩
    have h1 : (a^2 + b^2)^2 / (a^3 * b) ≥ 16 * Real.sqrt 3 / 9 := by
      have h2 : a > 0 := ha
      have h3 : b > 0 := hb
      have h4 : a^3 * b > 0 := by positivity
      have h5 : (a^2 + b^2) ^ 2 ≥ (16 * Real.sqrt 3 / 9) * (a^3 * b) := by
        nlinarith [sq_nonneg (a ^ 2 - 3 * b ^ 2), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 4 - 3 * a ^ 2 * b ^ 2), sq_nonneg (a * b - (Real.sqrt 3) * a * b), sq_nonneg (a * (a - Real.sqrt 3 * b)), sq_nonneg (b * (a - Real.sqrt 3 * b)), sq_nonneg (a ^ 2 - (3: ℝ) * b ^ 2), sq_nonneg (a - (Real.sqrt 3) * (b / 1)), sq_nonneg (a * Real.sqrt 3 - b), sq_nonneg (a * Real.sqrt 3 - 2 * b), sq_nonneg (2 * a * Real.sqrt 3 - 3 * b), sq_nonneg (a^2 - 3 * b^2), sq_nonneg (4 * a^2 - 3 * b^2), sq_nonneg (a * Real.sqrt 3 - b), sq_nonneg (a * Real.sqrt 3 - 2 * b), sq_nonneg (2 * a * Real.sqrt 3 - 3 * b), mul_pos ha hb, sq_nonneg (a^2 - (3: ℝ) * b^2), sq_nonneg ((a - Real.sqrt 3) * (a - Real.sqrt 3)), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by linarith), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by linarith)]
      apply (le_div_iff₀ h4).mpr
      nlinarith
    linarith [h_eq, h1]