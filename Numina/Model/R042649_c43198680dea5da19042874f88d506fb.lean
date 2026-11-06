import Mathlib

theorem algebra_306634 {x y z : ℝ} (h₀ : x + y + z = Real.sqrt (x + y + z + 1) + 5)
    (h₁ : x / 2 = y / 3) (h₂ : y / 3 = z / 4) :
    x = 16 / 9 ∧ y = 8 / 3 ∧ z = 32 / 9 := by

  have eq1 : 3 * x = 2 * y := by
    linarith
  have eq2 : 4 * y = 3 * z := by
    linarith

  have eq3 : z = 2 * x := by
    have h3 : y = (3 / 2) * x := by
      nlinarith
    rw [h3] at eq2
    linarith

  have eq4 : x + y + z = (9 / 2) * x := by
    have hy : y = (3 / 2) * x := by
      nlinarith
    have hz : z = 2 * x := by
      linarith
    rw [hy, hz]
    linarith

  have h₃ : (9 / 2) * x = Real.sqrt ((9 / 2) * x + 1) + 5 := by
    have h4 : x + y + z = (9 / 2) * x := by
      linarith [eq4]
    rw [h4] at h₀
    linarith

  by_cases h₆ : (9 / 2) * x + 1 ≥ 0
  · -- Assume argument of sqrt is ≥ 0
    have eq5 : Real.sqrt ((9 / 2) * x + 1) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h₇ : ( (9 / 2) * x - 5 ) = Real.sqrt ((9 / 2) * x + 1 ) := by
      linarith
    have h₈ : ( (9 / 2) * x - 5 ) ≥ 0 := by
      nlinarith [ h₇, eq5 ]
    have h₉ : ( (9 / 2) * x - 5 ) ^ 2 = ( Real.sqrt ((9 / 2) * x + 1 ) ) ^ 2 := by
      rw [ h₇ ]
    have h₁₁ : ( ( Real.sqrt ((9 / 2) * x + 1) ) ) ^ 2 = ( (9 / 2) * x + 1 ) := by
      rw [ Real.sq_sqrt ]
      linarith
    rw [ h₁₁ ] at h₉
    have h₁₃ : ( (9 / 2) * x ) = 8 ∨ ( (9 / 2) * x ) = 3 := by
      have h14 : ( (9 / 2) * x - 5 ) ^ 2 - ( (9 / 2) * x + 1 ) = 0 := by
        linarith [ h₉, h₁₁ ]
      have h15 : ( (9 / 2) * x - 8 ) * ( (9 / 2) * x - 3 ) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h15) with h16 h17
      · -- (9/2)x - 8 = 0
        left
        linarith
      · -- (9/2)x - 3 = 0
        right
        linarith
    cases h₁₃ with
    | inl h₈ =>
      have hx1 : x = 16 / 9 := by
        nlinarith
      have hy1 : y = 8 / 3 := by
        nlinarith
      have hz1 : z = 32 / 9 := by
        nlinarith
      constructor
      · exact hx1
      constructor
      · exact hy1
      · exact hz1
    | inr h₉ =>
      have hx1 : x = 2 / 3 := by
        nlinarith
      nlinarith [ Real.sqrt_nonneg ( (9 / 2) * x + 1 ), 
        Real.sq_sqrt (show (0 : ℝ) ≤ ( (9 / 2) * x + 1 ) by nlinarith ) 
      ]
  · -- Case where the argument of sqrt is < 0, which is impossible
    have h₇ : (9 / 2) * x + 1 < 0 := by
      linarith
    have h₈ : Real.sqrt ((9 / 2) * x + 1) = 0 := by
      rw [ Real.sqrt_eq_zero'.mpr (by linarith) ]
      all_goals 
        linarith
    nlinarith [ h₇, Real.sqrt_nonneg ( (9 / 2) * x + 1 ), h₈ ]