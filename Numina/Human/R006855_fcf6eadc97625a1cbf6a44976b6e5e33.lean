import Mathlib
open Real Finset Set 
noncomputable section

-- Definition given in the question (unused definitions).
def S : ℚ := 1/3 + 1/15 + 1/25 + 1/63 + 1/100 + 1/113

/-Let $S$ be the sum of the fractions $\frac{1}{3}, \frac{1}{15}, \frac{1}{25}, \frac{1}{63}, \frac{1}{100}, \frac{1}{113}$. Suppose that the product $S \times 2015$ is equal to $930$. Compute the value of the expression $S \times 4060225$. Show that the answer is $1873950$.-/
theorem algebra_20005 (h : S * 2015 = 930) : S * 4060225 = 1873950 := by
  -- Calculate $S$.
  have h_S : S = 930 / 2015 := by linarith

  -- Calculate $S * 4060225$.
  have h_product : S * 4060225 = (930 / 2015) * 4060225 := by
    rw [h_S]

  -- Simplify $930 / 2015$.
  have h_fraction_simp : (930: ℚ) / 2015 = 6 / 13 := by
    -- have h_gcd : Nat.gcd 930 2015 = 155 := by norm_num
    have h₁: (930 : ℚ) = 6 * 155 := by norm_num
    have h₂: (2015 : ℚ) = 13 * 155 := by norm_num
    rw [h₁, h₂]
    linarith

  -- Calculate $(6 / 13) * 4060225$.
  have h_calc : ((6 :ℚ ) / 13) * 4060225 = 6 * 4060225 / 13 := by
    have h_calc' : ((6 :ℚ )/ 13) * 4060225 = 6 * 4060225 / 13 := by
      rw [div_mul_eq_mul_div₀]
    exact_mod_cast h_calc'

  -- Verify $4060225 / 13$ and the final result.
  have h_div_13 : 4060225 = (13 : ℚ)  * 312325 := by norm_num
  have h_final : (6 :ℚ ) * 4060225 / 13 = 1873950 := by
    rw [h_div_13]
    linarith

  -- Combine all steps.
  rw [h_product, h_fraction_simp, h_calc, h_final]
