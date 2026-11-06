import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_320515 {f g : ℝ → ℝ}
  (hf : f = λ x => sqrt (3 * x ^ 2 + 7))
  (hg : g = λ x => x ^ 2 + 16 / (x ^ 2 + 1) - 1) :
  IsLeast {y | ∃ x, g (f x) = y} 8 := by
  constructor
  · -- Show 8 is in the set
    use 0
    rw [hf]
    rw [hg]
    have h1 : sqrt (3 * (0 : ℝ) ^ 2 + 7) = Real.sqrt 7 := by
      norm_num
    simp [h1]
    have h2 : (Real.sqrt 7 : ℝ) ^ 2 = 7 := Real.sq_sqrt (by norm_num)
    field_simp [h2]
    <;> nlinarith
  · -- Show there is no smaller element in the set
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [hf] at hx
    rw [hg] at hx
    simp at hx
    have h3 : (Real.sqrt (3 * x ^ 2 + 7) : ℝ) ^ 2 = 3 * x ^ 2 + 7 := by
      apply Real.sq_sqrt
      nlinarith [sq_nonneg x]
    have eq3 : (3 * x ^ 2 + 7 : ℝ) + 16 / ((3 * x ^ 2 + 7) + 1) - 1 = y := by
      rw [h3] at hx
      linarith
    have eq4 : (3 * x ^ 2 + 7 : ℝ) + 16 / ((3 * x ^ 2 + 7) + 1) - 1 = 3 * x^2 + 6 + 16 / (3 * x ^ 2 + 8) := by
      field_simp
      <;> ring
    have eq5 : 3 * x^2 + 6 + 16 / (3 * x ^ 2 + 8) = y := by
      linarith [eq3, eq4]
    have h4 : 3 * x^2 + 6 + 16 / (3 * x ^ 2 + 8) ≥ 8 := by
      have h5 : 0 < (3 * x ^ 2 + 8 : ℝ) := by
        nlinarith [sq_nonneg x]
      have h6 : 3 * x^2 + 6 + 16 / (3 * x ^ 2 + 8) - 8 ≥ 0 := by
        have h7 : (3 * x^2 + 6 + 16 / (3 * x ^ 2 + 8) - 8) = (3 * x ^ 2 - 2 + 16 / (3 * x ^ 2 + 8)) := by
          ring
        rw [h7]
        have h8 : 3 * x ^ 2 - 2 + 16 / (3 * x ^ 2 + 8) = ( (3 * x ^ 2) - 2 ) * (3 * x ^ 2 + 8) / (3 * x ^ 2 + 8) + 16 / (3 * x ^ 2 + 8) := by
          field_simp
          <;> ring
        rw [h8]
        have h9 : ( (3 * x ^ 2) - 2 ) * (3 * x ^ 2 + 8 ) / (3 * x ^ 2 + 8 ) + 16 / (3 * x ^ 2 + 8 ) = ( ( (3 * x ^ 2) - 2 ) * (3 * x ^ 2 + 8 ) + 16 ) / (3 * x ^ 2 + 8 ) := by
          ring
        rw [h9]
        apply div_nonneg
        · -- Show numerator is non-negative
          nlinarith [sq_nonneg (3 * x ^ 2), sq_nonneg ((3 * x ^ 2) - 2), sq_nonneg (x ^ 2 - 4 / 3), sq_nonneg (3 * x ^ 2 - 2)]
        · -- Show denominator is non-negative
          nlinarith [sq_nonneg x]
      linarith
    linarith [eq5, h4]