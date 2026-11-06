import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_156079 (f : ℝ → ℝ) (hf : f = λ x => sqrt (2 - x) + sqrt (3 * x + 12))
  (x : ℝ) (hx : x ∈ Icc (-4) 2) :
  f x ∈ Icc (sqrt 6) (2 * sqrt 6) := by
  rcases hx with ⟨hx1, hx2⟩
  have hfx1 : f x = sqrt (2 - x) + sqrt (3 * x + 12) := by
    rw [hf]
  have h1 : sqrt 6 ≤ sqrt (2 - x) + sqrt (3 * x + 12) := by
    have h21 : 0 ≤ (2 - x : ℝ) := by nlinarith
    have h31 : 0 ≤ (3 * x + 12 : ℝ) := by nlinarith
    have h41 : (sqrt (2 - x) + sqrt (3 * x + 12)) ^ 2 ≥ 6 := by
      have h5 : (sqrt (2 - x) + sqrt (3 * x + 12)) ^ 2 =
          (sqrt (2 - x)) ^ 2 + (sqrt (3 * x + 12)) ^ 2 + 2 * (sqrt (2 - x) * sqrt (3 * x + 12)) := by ring
      have h6 : (sqrt (2 - x)) ^ 2 = (2 - x) := by
        rw [Real.sq_sqrt]
        linarith
      have h7 : (sqrt (3 * x + 12)) ^ 2 = (3 * x + 12) := by
        rw [Real.sq_sqrt]
        nlinarith
      have h8 : sqrt (2 - x) * sqrt (3 * x + 12) ≥ 0 := by
        apply mul_nonneg
        · apply Real.sqrt_nonneg
        · apply Real.sqrt_nonneg
      have h9 : (sqrt (2 - x) + sqrt (3 * x + 12)) ^ 2 = (2 - x : ℝ) + (3 * x + 12 : ℝ) + 2 * (sqrt (2 - x) * sqrt (3 * x + 12)) := by
        linarith [h5, h6, h7]
      nlinarith [sq_nonneg (sqrt (2 - x) - sqrt (3 * x + 12)), sq_nonneg (x + 4), sq_nonneg (x - 2), 
        Real.sqrt_nonneg (2 - x), Real.sqrt_nonneg (3 * x + 12),
        Real.sq_sqrt (show (2 - x : ℝ) ≥ 0 by linarith), 
        Real.sq_sqrt (show (3 * x + 12 : ℝ) ≥ 0 by nlinarith), 
        mul_nonneg (Real.sqrt_nonneg (2 - x)) (Real.sqrt_nonneg (3 * x + 12))
      ]
    have h10 : sqrt 6 ≤ sqrt (2 - x) + sqrt (3 * x + 12) := by
      have h110 : sqrt 6 = Real.sqrt (6 : ℝ) := by rfl
      have h120 : sqrt (2 - x) + sqrt (3 * x + 12) ≥ Real.sqrt (6 : ℝ) := by
        have h132 : Real.sqrt (6 : ℝ) ≥ 0 := by positivity
        have h140 : (sqrt (2 - x) + sqrt (3 * x + 12)) ≥ 0 := by positivity
        have h150 : (sqrt (2 - x) + sqrt (3 * x + 12)) ^ 2 ≥ (Real.sqrt (6 : ℝ)) ^ 2 := by
          nlinarith [h41, Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num), 
            Real.sqrt_nonneg (2 - x), Real.sqrt_nonneg (3 * x + 12),
            mul_nonneg (Real.sqrt_nonneg (2 - x)) (Real.sqrt_nonneg (3 * x + 12))
          ]
        have h160 : sqrt (2 - x) + sqrt (3 * x + 12) ≥ Real.sqrt (6 : ℝ) := by
          nlinarith [Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (2 - x), Real.sqrt_nonneg (3 * x + 12), 
            Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num), 
            Real.sq_sqrt (show (2 - x : ℝ) ≥ 0 by linarith), 
            Real.sq_sqrt (show (3 * x + 12 : ℝ) ≥ 0 by nlinarith)
          ]
        linarith
      linarith [h120]
    linarith
  -- Now show the second part of the bounds
  have h2 : sqrt (2 - x) + sqrt (3 * x + 12) ≤ 2 * sqrt 6 := by
    have h31 : 0 ≤ (2 - x : ℝ) := by nlinarith
    have h41 : 0 ≤ (3 * x + 12 : ℝ) := by nlinarith
    have h21 : (sqrt (2 - x) + sqrt (3 * x + 12)) ^ 2 ≤ (2 * sqrt 6) ^ 2 := by
      have h5 : (sqrt (2 - x) + sqrt (3 * x + 12)) ^ 2 =
          (sqrt (2 - x)) ^ 2 + (sqrt (3 * x + 12)) ^ 2 + 2 * (sqrt (2 - x) * sqrt (3 * x + 12)) := by ring
      have h6 : (sqrt (2 - x)) ^ 2 = (2 - x) := by
        rw [Real.sq_sqrt]
        linarith
      have h7 : (sqrt (3 * x + 12)) ^ 2 = (3 * x + 12) := by
        rw [Real.sq_sqrt]
        nlinarith
      have h8 : (2 * sqrt 6) ^ 2 = (24 : ℝ) := by
        calc
          (2 * sqrt 6) ^ 2 = 4 * (sqrt 6) ^ 2 := by ring
          _ = 4 * 6 := by
            rw [Real.sq_sqrt]
            all_goals norm_num
          _ = (24 : ℝ) := by norm_num
      have h9 : (sqrt (2 - x) + sqrt (3 * x + 12)) ^ 2 = (2 - x : ℝ) + (3 * x + 12 : ℝ) + 2 * (sqrt (2 - x) * sqrt (3 * x + 12)) := by
        linarith [h5, h6, h7]
      nlinarith [sq_nonneg (sqrt (2 - x) - sqrt (3 * x + 12)), sq_nonneg (x - (1 / 2 : ℝ)), sq_nonneg (x - 2), sq_nonneg (x + 4),
        Real.sqrt_nonneg (2 - x), Real.sqrt_nonneg (3 * x + 12),
        Real.sq_sqrt (show (2 - x : ℝ) ≥ 0 by linarith),
        Real.sq_sqrt (show (3 * x + 12 : ℝ) ≥ 0 by nlinarith),
        mul_nonneg (Real.sqrt_nonneg (2 - x)) (Real.sqrt_nonneg (3 * x + 12))
      ]
    have h22 : sqrt (2 - x) + sqrt (3 * x + 12) ≤ 2 * sqrt 6 := by
      have h130 : (sqrt (2 - x) + sqrt (3 * x + 12)) ≥ 0 := by positivity
      have h140 : (2 * sqrt 6) ≥ 0 := by positivity
      have h150 : (sqrt (2 - x) + sqrt (3 * x + 12)) ^ 2 ≤ (2 * sqrt 6) ^ 2 := h21
      nlinarith [Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (2 - x), Real.sqrt_nonneg (3 * x + 12),
        Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num), 
        Real.sq_sqrt (show (2 - x : ℝ) ≥ 0 by linarith), 
        Real.sq_sqrt (show (3 * x + 12 : ℝ) ≥ 0 by nlinarith)
      ]
    linarith
  rw [hfx1]
  constructor
  · -- Show that sqrt 6 ≤ f x
    linarith [h1]
  · -- Show that f x ≤ 2 * sqrt 6
    linarith [h2]