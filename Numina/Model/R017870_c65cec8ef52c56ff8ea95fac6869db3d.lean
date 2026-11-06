import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_263637 :
  IsLeast {x | ∃ a : ℝ, x = sqrt (a^2 - 2*a + 5) + sqrt (a^2 - 4*a + 13)} (sqrt 26) := by
  constructor
  · -- Show that sqrt(26) is in the set
    use 7 / 5
    have h1 : Real.sqrt ( (7 / 5 : ℝ) ^2 - 2 * (7 / 5 : ℝ) + 5 ) = 2 * Real.sqrt (26) / 5 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    have h2 : Real.sqrt ( (7 / 5 : ℝ) ^2 - 4 * (7 / 5 : ℝ) + 13 ) = 3 * Real.sqrt (26) / 5 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [ h1, h2 ]
    linarith
  · -- Show that sqrt(26) is the minimum
    intro x hx
    rcases hx with ⟨a, ha⟩
    have h1 : sqrt (a^2 - 2*a + 5) + sqrt (a^2 - 4*a + 13) ≥ sqrt (26) := by
      have h2 : (sqrt (a^2 - 2*a + 5) + sqrt (a^2 - 4*a + 13)) ^ 2 ≥ (26 : ℝ) := by
        have h3 : sqrt (a^2 - 2*a + 5) ≥ 0 := Real.sqrt_nonneg (a^2 - 2*a + 5)
        have h4 : sqrt (a^2 - 4*a + 13) ≥ 0 := Real.sqrt_nonneg (a^2 - 4*a + 13)
        have h5 : (sqrt (a^2 - 2*a + 5) + sqrt (a^2 - 4*a + 13)) ^ 2 =
            (sqrt (a^2 - 2*a + 5)) ^ 2 + (sqrt (a^2 - 4*a + 13)) ^ 2 + 2 * (sqrt (a^2 - 2*a + 5) * sqrt (a^2 - 4*a + 13)) := by ring
        rw [h5]
        have h6 : (sqrt (a^2 - 2*a + 5)) ^ 2 = a ^ 2 - 2*a + 5 := Real.sq_sqrt (by nlinarith)
        have h7 : (sqrt (a^2 - 4*a + 13)) ^ 2 = a ^ 2 - 4*a + 13 := Real.sq_sqrt (by nlinarith)
        rw [h6, h7]
        nlinarith [ sq_nonneg (a - 7 / 5), sq_nonneg (a + 1), 
          sq_nonneg (sqrt (a^2 - 2*a + 5) - 2 * Real.sqrt 26 / 5), 
          sq_nonneg (sqrt (a^2 - 4*a + 13) - 3 * Real.sqrt 26 / 5), 
          Real.sqrt_nonneg (26), 
          sq_nonneg (a^2 -2*a +5 -104/25), 
          sq_nonneg (a^2 -4*a +13 -234/25), 
          mul_nonneg (Real.sqrt_nonneg (a^2 - 2*a + 5)) (Real.sqrt_nonneg (a^2 -4*a +13)), 
          h6, h7
        ]
      have h3 : sqrt (a^2 - 2*a + 5) + sqrt (a^2 - 4*a + 13) ≥ sqrt (26) := by
        have h4 : (sqrt (a^2 - 2*a + 5) + sqrt (a^2 - 4*a + 13)) ^ 2 ≥ (26 : ℝ) := h2
        have h5 : sqrt (26) ≥ 0 := Real.sqrt_nonneg 26
        have h6 : sqrt (a^2 - 2*a + 5) + sqrt (a^2 - 4*a + 13) ≥ 0 := by positivity
        have h7 : sqrt (a^2 - 2*a + 5) + sqrt (a^2 - 4*a + 13) ≥ sqrt (26) := by
          nlinarith [ sq_nonneg (sqrt (a^2 - 2*a + 5) + sqrt (a^2 - 4*a + 13) - sqrt (26)), 
            Real.sqrt_nonneg (26), 
            Real.sq_sqrt (show (0 : ℝ) ≤ (26 : ℝ) by norm_num)
          ]
        exact h7
      exact h3
    linarith [ Real.sqrt_nonneg (26), h1, Real.sqrt_nonneg (a ^ 2 - 2*a +5), Real.sqrt_nonneg (a ^ 2 - 4*a +13) ]