import Mathlib

theorem algebra_5683 :
  IsGreatest {y : ℤ | ∃ x : ℝ, y = 2244 / (x ^ 2 - 12 * x + 67)} 72 := by
  constructor
  · -- Show 72 is in the set.
    use 6 + Real.sqrt 6 / 6
    have h1 : (6 + Real.sqrt 6 / 6 : ℝ) ^ 2 - 12 * (6 + Real.sqrt 6 / 6 : ℝ) + 67 = (187 / 6 : ℝ) := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 6 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)]
    have h2 : (2244 : ℝ) / (187 / 6 : ℝ) = (72 : ℝ) := by
      field_simp
      <;> norm_num
    rw [h1]
    norm_num at h2 ⊢
    <;> nlinarith [h2]
  · -- Show 72 is greatest in the set.
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h1 : x ^ 2 - 12 * x + 67 > 0 := by
      nlinarith [sq_nonneg (x - 6)]
    have eq2 : (y : ℝ) * (x ^ 2 - 12 * x + 67) = (2244 : ℝ) := by
      have eq : (y : ℝ) = (2244 / (x ^ 2 - 12 * x + 67) : ℝ) := by linarith [hx]
      field_simp [(show x ^ 2 - 12 * x + 67 ≠ 0 by 
        by_contra h0
        have : x ^ 2 - 12 * x + 67 = (0 : ℝ) := by linarith
        nlinarith [sq_nonneg (x - 6)]
      )] at eq ⊢
      nlinarith [eq]
    by_contra h
    push_neg at h
    have h2 : y ≥ 73 := by omega
    have h3 : (y : ℝ) ≥ (73 : ℝ) := by
      exact_mod_cast h2
    nlinarith [sq_nonneg (x - 6), sq_nonneg ((x - 6) * (y : ℝ)), sq_nonneg ((x - 6) - (y : ℝ) * (x - 6) / (y : ℝ)), sq_nonneg ((y : ℝ) * (x - 6)), sq_nonneg ((y : ℝ) - 73), sq_nonneg ((x - 6) - (y : ℝ) / (y : ℝ) * (x - 6))]