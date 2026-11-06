import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_37945 :
  IsLeast {x : ℝ | ∃ a : ℝ, x = (16 * a ^ 4 + 40 * a ^ 3 + 41 * a ^ 2 + 20 * a + 16) / (4 * a ^ 2 + 5 * a + 2)} (4 * sqrt 3) := by
  constructor
  · -- Show that 4 * sqrt 3 is in the set
    use (-5 + Real.sqrt (-7 +32* Real.sqrt 3 )) / 8
    have h0 : (-7 + 32 * Real.sqrt 3 : ℝ) ≥ 0 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    have h1 : Real.sqrt (-7 +32* Real.sqrt 3 ) ≥ 0 := Real.sqrt_nonneg (-7 +32* Real.sqrt 3 )
    have h2 : 4 * ((-5 + Real.sqrt (-7 +32* Real.sqrt 3 )) / 8) ^ 2 + 5 * ((-5 + Real.sqrt (-7 +32* Real.sqrt 3 )) / 8) + 2 = 2 * Real.sqrt 3 := by
      nlinarith [ Real.sqrt_nonneg (-7 +32* Real.sqrt 3 ), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (-7 +32* Real.sqrt 3 : ℝ) by linarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]) ]
    have eq1 : (16 * ((-5 + Real.sqrt (-7 +32* Real.sqrt 3 )) / 8) ^ 4 + 40 * ((-5 + Real.sqrt (-7 +32* Real.sqrt 3 )) / 8) ^ 3 + 41 * ((-5 + Real.sqrt (-7 +32* Real.sqrt 3 )) / 8) ^ 2 + 20 * ((-5 + Real.sqrt (-7 +32* Real.sqrt 3 )) / 8) + 16) / (4 * ((-5 + Real.sqrt (-7 +32* Real.sqrt 3 )) / 8) ^ 2 + 5 * ((-5 + Real.sqrt (-7 +32* Real.sqrt 3 )) / 8) + 2) = 4 * Real.sqrt 3 := by
      have h3 : (4 * ((-5 + Real.sqrt (-7 +32* Real.sqrt 3 )) / 8) ^ 2 + 5 * ((-5 + Real.sqrt (-7 +32* Real.sqrt 3 )) / 8) + 2) = 2 * Real.sqrt 3 := h2
      have h4 :16 * ((-5 + Real.sqrt (-7 +32* Real.sqrt 3 )) / 8) ^ 4 + 40 * ((-5 + Real.sqrt (-7 +32* Real.sqrt 3 )) / 8) ^ 3 + 41 * ((-5 + Real.sqrt (-7 +32* Real.sqrt 3 )) / 8) ^ 2 + 20 * ((-5 + Real.sqrt (-7 +32* Real.sqrt 3 )) / 8) + 16 = (2 * Real.sqrt 3) ^ 2 +12 := by
        nlinarith [ Real.sqrt_nonneg (-7 +32* Real.sqrt 3 ), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (-7 +32* Real.sqrt 3 : ℝ) by linarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]) ]
      rw [ h4, h3 ]
      field_simp
      <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    linarith
  · -- Show that 4 * sqrt 3 is the smallest element in the set
    intro x hx
    rcases hx with ⟨a, hx⟩
    have h2 : 4 * a ^ 2 + 5 * a + 2 > 0 := by
      nlinarith [ sq_nonneg (a * 4 + 5 / 2 ), sq_nonneg (a + 5 / 8 ), sq_nonneg ( a ), sq_nonneg ( a + 5 / 4 ), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num) ]
    have h3 : (16 * a ^ 4 + 40 * a ^ 3 + 41 * a ^ 2 + 20 * a + 16) / (4 * a ^ 2 + 5 * a + 2) ≥ 4 * Real.sqrt 3 := by
      have eq1 : (16 * a ^ 4 + 40 * a ^ 3 + 41 * a ^ 2 + 20 * a + 16) = (4 * a ^ 2 + 5 * a + 2) ^ 2 + 12 := by
        nlinarith
      rw [eq1]
      have h4 : (4 * a ^ 2 + 5 * a + 2) ^ 2 + 12 ≥ 4 * Real.sqrt 3 * (4 * a ^ 2 + 5 * a + 2) := by
        nlinarith [ sq_nonneg ((4 * a ^ 2 + 5 * a + 2) - 2 * Real.sqrt 3 ), sq_nonneg (Real.sqrt 3), Real.sqrt_nonneg 3, mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num) ]
      have h5 : (4 * a ^ 2 + 5 * a + 2) > 0 := h2
      have h6 : ( (4 * a ^ 2 + 5 * a + 2 ) ^ 2 + 12 ) / (4 * a ^ 2 + 5 * a + 2) ≥ 4 * Real.sqrt 3 := by
        apply (le_div_iff₀ h2).mpr
        nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num) ]
      linarith
    linarith [ h3, hx ]