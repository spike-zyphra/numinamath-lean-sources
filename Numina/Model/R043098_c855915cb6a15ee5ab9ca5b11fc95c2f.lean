import Mathlib

open Real Set

theorem inequalities_319474 (a : ℝ) :
    (∀ x y : ℝ, a * (x + y) ≤ 1 + x ^ 2 + x * y + y ^ 2) ↔
    a ∈ Icc (-sqrt 3) (sqrt 3) := by
  constructor
  · -- Assume that for all x, y, a*(x + y) ≤ 1 + x^2 + x * y + y^2, prove that a ∈ Icc (-sqrt 3) (sqrt 3)
    intro h
    have h1 : a ^ 2 ≤ 3 := by
      specialize h (a / 3) (a / 3)
      nlinarith [sq_nonneg (a / 3 - a / 3), sq_nonneg (a / 3 + a / 3 - a), sq_nonneg (a ^ 2 - 3) ]
    constructor
    · -- Show $-\sqrt{3} \leq a$
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (a + sqrt 3) ]
    · -- Show $a \leq \sqrt{3}$
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (a - sqrt 3) ]
  · -- Show the reverse: if a ∈ Icc (-sqrt 3) (sqrt 3), then ∀ x y : ℝ, a * (x + y) ≤ 1 + x ^ 2 + x * y + y ^ 2
    rintro ⟨h1, h2⟩
    intro x y
    have h3 : a ^ 2 ≤ 3 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (a ^ 2 - 3) ]
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - a * 2 / 3), sq_nonneg (a ^ 2 - 3), 
                Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
                sq_nonneg (x - a / 3), sq_nonneg (y - a / 3), Real.sqrt_nonneg 3
    ]