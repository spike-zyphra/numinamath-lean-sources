import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_325638 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
  (f : ℝ → ℝ) (hf : f = λ x => a * abs (sin x) + b * abs (cos x)) :
  ∀ x, f x ∈ Icc a (Real.sqrt (a^2 + b^2)) ∪ Icc b (Real.sqrt (a^2 + b^2)) := by
  intro x
  have h1 : f x = a * abs (sin x) + b * abs (cos x) := by
    rw [hf]
  have h2 : 0 ≤ abs (sin x) := abs_nonneg (sin x)
  have h3 : 0 ≤ abs (cos x) := abs_nonneg (cos x)
  have h4 : (abs (sin x)) ^ 2 + (abs (cos x)) ^ 2 = 1 := by
    have h5 : sin x ^ 2 + cos x ^ 2 = 1 := by 
      exact Real.sin_sq_add_cos_sq x
    have h6 : abs (sin x) ^ 2 = sin x ^ 2 := by 
      rw [sq_abs]
    have h7 : abs (cos x) ^ 2 = cos x ^ 2 := by 
      rw [sq_abs]
    linarith [h5, h6, h7]
  have h5 : f x ≤ Real.sqrt (a^2 + b^2) := by
    rw [h1]
    nlinarith [sq_nonneg (a * abs (cos x) - b * abs (sin x)), sq_nonneg (a - b), sq_nonneg (abs (sin x) - abs (cos x)), 
      Real.sqrt_nonneg (a^2 + b^2), Real.sq_sqrt (show 0 ≤ a^2 + b^2 by nlinarith), 
      mul_pos ha hb, h2, h3
    ]
  by_cases h7 : a ≤ b
  · -- Case a ≤ b
    have h8 : a ≤ f x := by
      rw [h1]
      have h9 : abs (sin x) + abs (cos x) ≥ 1 := by
        have h10 : (abs (sin x) + abs (cos x)) ^ 2 ≥ 1 := by
          nlinarith [sq_nonneg (abs (sin x) - abs (cos x)), h4, h2, h3]
        nlinarith [sq_nonneg (abs (sin x) + abs (cos x) - 1)]
      nlinarith [abs_nonneg (sin x), abs_nonneg (cos x), h2, h3, ha, hb, h7]
    left
    constructor
    · linarith [h8]
    · linarith [h5]
  · -- Case b < a
    have h8 : b ≤ f x := by
      rw [h1]
      have h9 : abs (sin x) + abs (cos x) ≥ 1 := by
        have h10 : (abs (sin x) + abs (cos x)) ^ 2 ≥ 1 := by
          nlinarith [sq_nonneg (abs (sin x) - abs (cos x)), h4, h2, h3]
        nlinarith [sq_nonneg (abs (sin x) + abs (cos x) - 1)]
      nlinarith [abs_nonneg (sin x), abs_nonneg (cos x), h2, h3, ha, hb, 
        show b ≤ a by linarith
      ]
    right
    constructor
    · linarith [h8]
    · linarith [h5]