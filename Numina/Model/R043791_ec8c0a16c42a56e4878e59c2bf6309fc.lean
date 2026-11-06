import Mathlib

theorem algebra_113204 (x y : ℝ) (h : 3 * x ^ 2 + 4 * y ^ 2 = 1) (lambda : ℝ)
    (h' : |3 * x + 4 * y - lambda| + |lambda + 7 - 3 * x - 4 * y| = 1) :
    lambda ∈ Set.Icc (Real.sqrt 7 - 7) (-Real.sqrt 7) := by
  have h1 : |3 * x + 4 * y - lambda| + |lambda + 7 - 3 * x - 4 * y| ≥ 7 := by 
    have h2 : |3 * x + 4 * y - lambda| + |lambda + 7 - 3 * x - 4 * y| ≥ 
        |(3 * x + 4 * y - lambda) + (lambda + 7 - 3 * x - 4 * y)| := by 
      apply abs_add
    have h3 : (3 * x + 4 * y - lambda) + (lambda + 7 - 3 * x - 4 * y) = 7 := by 
      ring
    have h4 : |(3 * x + 4 * y - lambda) + (lambda + 7 - 3 * x - 4 * y)| = 7 := by 
      rw [h3]
      norm_num
    linarith [h2, h4]
  linarith