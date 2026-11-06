import Mathlib

theorem inequalities_6918 (n : ℕ) :
    (0 < n → √(4 * n + 1) < √n + √(n + 1) ∧ √n + √(n + 1) < √(4 * n + 2)) := by
  intro hn
  have h1 : (n : ℝ) > (0 : ℝ) := by exact_mod_cast hn
  have h21 : √(4 * (n : ℝ) + 1 : ℝ) < √(n : ℝ) + √(n + 1 : ℝ) := by
    have h3 : (4 * (n : ℝ) + 1 : ℝ) < (√(n : ℝ) + √(n + 1 : ℝ)) ^ 2 := by
      have h31 : (√(n : ℝ) + √(n + 1 : ℝ) : ℝ) ^ 2 = (√(n : ℝ)) ^ 2 + (√(n + 1 : ℝ)) ^ 2 + 2 * (√(n : ℝ) * √(n + 1 : ℝ)) := by ring
      rw [h31]
      have h32 : (√(n : ℝ) : ℝ) ^ 2 = (n : ℝ) := by
        exact Real.sq_sqrt (by linarith)
      have h33 : (√(n + 1 : ℝ) : ℝ) ^ 2 = (n + 1 : ℝ) := by
        exact Real.sq_sqrt (by linarith)
      have h34 : √(n : ℝ) * √(n + 1 : ℝ) = √((n : ℝ) * (n + 1 : ℝ)) := by
        rw [Real.sqrt_mul (by nlinarith [Real.sqrt_nonneg (n : ℝ), Real.sqrt_nonneg (n + 1 : ℝ)])]
      rw [h32, h33, h34]
      nlinarith [Real.sqrt_pos.mpr (by nlinarith : (n : ℝ) * (n + 1 : ℝ) > 0), Real.sq_sqrt (show (n : ℝ) * (n + 1 : ℝ) ≥ 0 by nlinarith [Real.sqrt_nonneg ((n : ℝ) * (n + 1 : ℝ))])]
    have h44 : √(4 * (n : ℝ) + 1) ^ 2 < (√(n : ℝ) + √(n + 1 : ℝ)) ^ 2 := by
      have h45 : √(4 * (n : ℝ) + 1) ^ 2 = (4 * (n : ℝ) + 1 : ℝ) := by
        exact Real.sq_sqrt (by nlinarith)
      nlinarith [h3, Real.sqrt_nonneg (4 * (n : ℝ) + 1 : ℝ), Real.sqrt_nonneg (n : ℝ), Real.sqrt_nonneg (n + 1 : ℝ)]
    nlinarith [Real.sqrt_nonneg (4 * (n : ℝ) + 1 : ℝ), Real.sqrt_nonneg (n : ℝ), Real.sqrt_nonneg (n + 1 : ℝ)]
  have h45 : √(n : ℝ) + √(n + 1 : ℝ) < √(4 * (n : ℝ) + 2 : ℝ) := by
    have h4 : (√(n : ℝ) + √(n + 1 : ℝ) : ℝ) ^ 2 < (4 * (n : ℝ) + 2 : ℝ) := by
      have h31 : (√(n : ℝ) + √(n + 1 : ℝ) : ℝ) ^ 2 = (√(n : ℝ)) ^ 2 + (√(n + 1 : ℝ)) ^ 2 + 2 * (√(n : ℝ) * √(n + 1 : ℝ)) := by ring
      rw [h31]
      have h32 : (√(n : ℝ) : ℝ) ^ 2 = (n : ℝ) := by
        exact Real.sq_sqrt (by linarith)
      have h33 : (√(n + 1 : ℝ) : ℝ) ^ 2 = (n + 1 : ℝ) := by
        exact Real.sq_sqrt (by linarith)
      have h34 : √(n : ℝ) * √(n + 1 : ℝ) = √((n : ℝ) * (n + 1 : ℝ)) := by
        rw [Real.sqrt_mul (by nlinarith [Real.sqrt_nonneg (n : ℝ), Real.sqrt_nonneg (n + 1 : ℝ)])]
      rw [h32, h33, h34]
      nlinarith [Real.sqrt_nonneg ((n : ℝ) * (n + 1 : ℝ)), Real.sq_sqrt (show (n : ℝ) * (n + 1 : ℝ) ≥ 0 by nlinarith [Real.sqrt_nonneg ((n : ℝ) * (n + 1 : ℝ))]), sq_nonneg (√((n : ℝ) * (n + 1 : ℝ)) - (n + 1 / 2 : ℝ))]
    have h46 : (√(n : ℝ) + √(n + 1 : ℝ)) ^ 2 < √(4 * (n : ℝ) + 2) ^ 2 := by
      have h47 : √(4 * (n : ℝ) + 2) ^ 2 = (4 * (n : ℝ) + 2 : ℝ) := by
        exact Real.sq_sqrt (by nlinarith)
      nlinarith [h4, Real.sqrt_nonneg (4 * (n : ℝ) + 2 : ℝ), Real.sqrt_nonneg (n : ℝ), Real.sqrt_nonneg (n + 1 : ℝ)]
    nlinarith [Real.sqrt_nonneg (4 * (n : ℝ) + 2 : ℝ), Real.sqrt_nonneg (n : ℝ), Real.sqrt_nonneg (n + 1 : ℝ)]
  constructor
  · -- First part of the conjunction: $\sqrt{4n+1} < \sqrt{n} + \sqrt{n+1}$
    exact_mod_cast h21
  · -- Second part of the conjunction: $\sqrt{n} + \sqrt{n+1} < \sqrt{4n+2}$
    exact_mod_cast h45