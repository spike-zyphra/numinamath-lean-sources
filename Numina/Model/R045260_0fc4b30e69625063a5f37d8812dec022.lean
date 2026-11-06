import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_193087 :
  IsLeast {y | ∃ x : ℝ, y = sqrt (x^2 - 2*x + 5) + sqrt (x^2 - 4*x + 13)} (sqrt 26) := by
  constructor
  · -- Show that sqrt 26 is in the set
    use 7 / 5
    have h1 : sqrt ((7 / 5 : ℝ)^2 - 2 * (7 / 5 : ℝ) + 5) = 2 * sqrt 26 / 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    have h2 : sqrt ((7 / 5 : ℝ)^2 - 4 * (7 / 5 : ℝ) + 13) = 3 * sqrt 26 / 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h1, h2]
    linarith
  · -- Show that sqrt 26 is the least element in the set
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h2 : (x^2 - 2 * x + 5 : ℝ) = (x - 1)^2 + 4 := by
      ring_nf
    have h3 : (x^2 - 4 * x + 13 : ℝ) = (x - 2)^2 + 9 := by
      ring_nf
    have h4 : sqrt (x^2 - 2 * x + 5) = sqrt ((x - 1)^2 + 4) := by
      rw [h2]
    have h5 : sqrt (x^2 - 4 * x + 13) = sqrt ((x - 2)^2 + 9) := by
      rw [h3]
    have h6 : sqrt ((x - 1)^2 + 4) + sqrt ((x - 2)^2 + 9) ≥ sqrt 26 := by
      have h10 : (sqrt ((x - 1)^2 + 4) + sqrt ((x - 2)^2 + 9))^2 ≥ (sqrt 26)^2 := by
        have h7 : sqrt ((x - 1)^2 + 4) ≥ 0 := Real.sqrt_nonneg ((x - 1)^2 + 4)
        have h8 : sqrt ((x - 2)^2 + 9) ≥ 0 := Real.sqrt_nonneg ((x - 2)^2 + 9)
        have h9 : sqrt 26 ≥ 0 := Real.sqrt_nonneg 26
        have h11 : (sqrt ((x - 1)^2 + 4) + sqrt ((x - 2)^2 + 9))^2 = (sqrt ((x - 1)^2 + 4))^2 + (sqrt ((x - 2)^2 + 9))^2 + 2 * (sqrt ((x - 1)^2 + 4) * sqrt ((x - 2)^2 + 9)) := by
          ring
        have h12 : (sqrt 26)^2 = 26 := Real.sq_sqrt (by norm_num)
        rw [h11, h12]
        have h13 : (sqrt ((x - 1)^2 + 4))^2 = (x - 1)^2 + 4 := by
          rw [Real.sq_sqrt]
          positivity
        have h14 : (sqrt ((x - 2)^2 + 9))^2 = (x - 2)^2 + 9 := by
          rw [Real.sq_sqrt]
          positivity
        rw [h13, h14]
        nlinarith [sq_nonneg (sqrt ((x - 1)^2 + 4) - sqrt ((x - 2)^2 + 9)), sq_nonneg ((x - 7 / 5) * 5),
          Real.sqrt_nonneg 26, Real.sq_sqrt (show (0 : ℝ) ≤ 26 by norm_num), sq_nonneg (sqrt ((x - 1)^2 + 4) * sqrt ((x - 2)^2 + 9)), 
          mul_nonneg (Real.sqrt_nonneg ((x - 1)^2 + 4)) (Real.sqrt_nonneg ((x - 2)^2 + 9))
        ]
      have h7 : sqrt ((x - 1)^2 + 4) + sqrt ((x - 2)^2 + 9) ≥ 0 := by
        positivity
      have h8 : sqrt 26 ≥ 0 := Real.sqrt_nonneg 26
      nlinarith [h10, h7, h8]
    linarith [h4, h5, h6, hx]