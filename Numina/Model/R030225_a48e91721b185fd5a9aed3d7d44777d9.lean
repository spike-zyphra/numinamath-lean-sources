import Mathlib

open Real Set

theorem algebra_325694 (f : ℝ → ℝ) (hf : f = fun x => sqrt (x^2 + 4) + sqrt (x^2 - 4 * x + 5)) :
    IsLeast {y | ∃ x, f x = y} (sqrt 13) := by
  constructor
  · -- Show that sqrt 13 is in the range of f
    use 4 / 3
    rw [hf]
    have h1 : sqrt ((4 / 3 : ℝ) ^ 2 + 4) = (2 / 3) * sqrt 13 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num
    have h2 : sqrt ((4 / 3 : ℝ) ^ 2 - 4 * (4 / 3 : ℝ) + 5) = (1 / 3) * sqrt 13 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num
    simp only [h1, h2]
    ring_nf
  · -- Show that sqrt 13 is the least such value
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [hf] at hx
    simp at hx
    have h3 : sqrt (x ^ 2 + 4) + sqrt (x ^ 2 - 4 * x + 5) ≥ sqrt 13 := by
      have h4 : (sqrt (x ^ 2 + 4) + sqrt (x ^ 2 - 4 * x + 5)) ^ 2 ≥ 13 := by
        have h5 : (sqrt (x^2 + 4) + sqrt (x^2 - 4 * x + 5)) ^ 2 =
            (sqrt (x^2 + 4)) ^ 2 + (sqrt (x ^ 2 - 4 * x + 5)) ^ 2 + 2 * (sqrt (x ^ 2 + 4)) * (sqrt (x ^ 2 - 4 * x + 5)) := by
          ring
        rw [h5]
        have h6 : (sqrt (x^2 + 4)) ^ 2 = x^2 + 4 := by
          rw [Real.sq_sqrt]
          positivity
        have h7 : (sqrt (x ^ 2 - 4 * x + 5)) ^ 2 = x ^ 2 - 4 * x + 5 := by
          rw [Real.sq_sqrt]
          nlinarith [sq_nonneg (x - 2)]
        rw [h6, h7]
        have h8 : (x ^ 2 + 4) + (x ^ 2 - 4 * x + 5) + 2 * (sqrt (x ^ 2 + 4)) * (sqrt (x ^ 2 - 4 * x + 5)) ≥ 13 := by
          nlinarith [sq_nonneg (sqrt (x ^ 2 + 4) - sqrt (x ^ 2 - 4 * x + 5)), 
              sq_nonneg (x - 4 / 3),
              Real.sqrt_nonneg (x ^ 2 + 4), Real.sqrt_nonneg (x ^ 2 - 4 * x + 5),
              mul_nonneg (Real.sqrt_nonneg (x ^ 2 + 4)) (Real.sqrt_nonneg (x ^ 2 - 4 * x + 5)),
              Real.sq_sqrt (show (0 : ℝ) ≤ x^2 + 4 by positivity),
              Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 - 4 * x + 5 by nlinarith [sq_nonneg (x - 2)]),
              sq_nonneg (sqrt (x ^ 2 + 4) ^ 2 - sqrt (x ^ 2 - 4 * x + 5) ^ 2)
              ]
        linarith
      have h10 : sqrt (x ^ 2 + 4) + sqrt (x ^ 2 - 4 * x + 5) ≥ 0 := by
        positivity
      have h11 : sqrt 13 ≥ 0 := by
        positivity
      have h12 : (sqrt 13) ^ 2 = 13 := Real.sq_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg 13]
    linarith [h3, hx]