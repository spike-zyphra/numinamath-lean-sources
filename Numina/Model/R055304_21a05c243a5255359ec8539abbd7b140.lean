import Mathlib

open Real

theorem inequalities_298739 (a b : ℝ) :
    sqrt (a ^ 2 + b ^ 2) ≤ abs a + abs b := by
  have h2 : (a ^ 2 + b ^ 2) ≤ (abs a + abs b) ^ 2 := by
    have h3 : (abs a) ^ 2 = a ^ 2 := by
      rw [sq_abs]
    have h4 : (abs b) ^ 2 = b ^ 2 := by
      rw [sq_abs]
    have h5 : (abs a + abs b) ^ 2 = (abs a) ^ 2 + (abs b) ^ 2 + 2 * (abs a * abs b) := by
      ring
    rw [h5]
    rw [h3, h4]
    have h6 : abs a ≥ 0 := by apply abs_nonneg
    have h7 : abs b ≥ 0 := by apply abs_nonneg
    nlinarith [abs_nonneg a, abs_nonneg b, sq_nonneg (abs a - abs b)]
  
  have h4 : sqrt (a ^ 2 + b ^ 2) ≤ sqrt ((abs a + abs b) ^ 2) := by
    apply Real.sqrt_le_sqrt
    nlinarith [h2]

  have h5 : sqrt ((abs a + abs b) ^ 2) = abs a + abs b := by
    have h6 : abs a ≥ 0 := by apply abs_nonneg
    have h7 : abs b ≥ 0 := by apply abs_nonneg
    have h8 : (abs a + abs b) ≥ 0 := by
      linarith [h6, h7]
    rw [Real.sqrt_sq (by linarith [h6, h7])]

  linarith [h4, h5]
  all_goals
    try { nlinarith }
    try { linarith [abs_nonneg a, abs_nonneg b, sq_nonneg a, sq_nonneg b, sq_nonneg (a - b), sq_nonneg (a + b)] }
    try { tauto }