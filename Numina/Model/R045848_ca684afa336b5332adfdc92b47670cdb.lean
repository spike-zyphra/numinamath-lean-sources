import Mathlib

theorem number_theory_243628 (n : ℕ) (hn : n > 100) :
    (⌊(√(n ^ 2 + 3 * n + 1)) * 100⌋) % 100 = 49 := by 
  have h1 : (n : ℝ) > (100 : ℝ) := by 
    exact_mod_cast hn 
  have h2 : (n : ℝ) ^ 2 + 3 * (n : ℝ) + 1 > (n + 1 : ℝ) ^ 2 := by 
    nlinarith 
  -- show sqrt n^2+3n+1> n+1
  have h3 : √ ((n : ℝ) ^ 2 + 3 * (n : ℝ) + 1) > (n + 1 : ℝ) := by
    have h4 : (n : ℝ) ^ 2 + 3 * (n : ℝ) + 1 > (n + 1 : ℝ) ^ 2 := h2
    have h5 : √ ((n : ℝ) ^ 2 + 3 * (n : ℝ) + 1) > √ ((n + 1 : ℝ) ^ 2) := by
      apply Real.sqrt_lt_sqrt 
      all_goals nlinarith 
    have h6 : √ ((n + 1 : ℝ) ^ 2) = (n + 1 : ℝ) := Real.sqrt_sq (by linarith)
    linarith [h5, h6] 
  -- lower and upper bound sqrt n^2+3n+1
  have h7 : (n ^ 2 + 3 * n + 1 : ℝ) < ((n + 1.5) : ℝ) ^ 2 := by 
    nlinarith 
  have h8 : √ ((n ^ 2 + 3 * n + 1 : ℝ)) < (n + 1.5 : ℝ) := by
    nlinarith [Real.sqrt_nonneg ((n ^ 2 + 3 * n + 1 : ℝ)), Real.sq_sqrt (show (n ^ 2 + 3 * n + 1 : ℝ) ≥ 0 by positivity)]
  have h15 : ⌊(√(n ^ 2 + 3 * n + 1) * 100 : ℝ)⌋ = ( (n + 1) * 100 + 49 : ℤ) := by
    have h30 : (n + 1 : ℝ) * 100 + 49 < (√ ((n ^ 2 + 3 * n + 1 : ℝ)) ) * 100 := by 
      nlinarith [Real.sqrt_nonneg ((n ^ 2 + 3 * n + 1 : ℝ)), Real.sq_sqrt (show (n ^ 2 + 3 * n + 1 : ℝ) ≥ 0 by positivity), 
          h2, h7]
    have h31 : (√ ((n ^ 2 + 3 * n + 1 : ℝ)) ) * 100 < ((n + 1 : ℝ) * 100 + 50) := by
      nlinarith [Real.sqrt_nonneg ((n ^ 2 + 3 * n + 1 : ℝ)), Real.sq_sqrt (show (n ^ 2 + 3 * n + 1 : ℝ) ≥ 0 by positivity), 
          h7]
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith
  rw [h15]
  simp [Int.add_emod, Int.mul_emod]
  <;> ring_nf <;> omega