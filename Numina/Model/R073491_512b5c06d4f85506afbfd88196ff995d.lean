import Mathlib

theorem algebra_153688 (x : ℝ) (hx : 0 ≤ x - 1) (h : Real.sqrt (2 * x + 5) + Real.sqrt (x - 1) = 8) :
    x = 10 := by
  have h1 : Real.sqrt (2 * x + 5) ≥ 0 := by positivity
  have h2 : Real.sqrt (x - 1) ≥ 0 := by positivity
  have h3 : Real.sqrt (2 * x + 5) = 8 - Real.sqrt (x - 1) := by linarith [h]
  have h4 : 2 * x + 5 = (8 - Real.sqrt (x - 1)) ^ 2 := by
    calc
      2 * x + 5 = (Real.sqrt (2 * x + 5)) ^ 2 := by
        rw [Real.sq_sqrt]
        have : 0 ≤ 2 * x + 5 := by linarith [show 0 ≤ (x - 1) by linarith]
        linarith
      _ = (8 - Real.sqrt (x - 1)) ^ 2 := by rw [h3]
  have h5 : (8 - Real.sqrt (x - 1)) ^ 2 = 64 - 16 * Real.sqrt (x - 1) + (Real.sqrt (x - 1) ^ 2) := by ring
  have h6 : 2 * x + 5 = 64 - 16 * Real.sqrt (x - 1) + (x - 1) := by 
    rw [h4, h5]
    have h56 : (Real.sqrt (x - 1)) ^ 2 = x - 1 := by
      apply Real.sq_sqrt
      linarith
    rw [h56]
    all_goals 
      nlinarith
  have h7 : x - 58 = -16 * Real.sqrt (x - 1) := by
    nlinarith [h6, h2, h1]
  have h8 : Real.sqrt (x - 1) ≥ 0 := by positivity
  have h9 : 0 ≤ x := by linarith [hx]
  have h10 : 58 - x = 16 * Real.sqrt (x - 1) := by
    nlinarith [h7, h2]
  have h11 : (58 - x) ^ 2 = (16 * Real.sqrt (x - 1)) ^ 2 := by
    rw [h10]
  have h12 : (58 - x) ^ 2 = 256 * (x - 1) := by
    calc
      (58 - x) ^ 2 = (16 * Real.sqrt (x - 1)) ^ 2 := h11
      _ = (16 ^ 2) * (Real.sqrt (x - 1) ^ 2) := by ring
      _ = (256) * (Real.sqrt (x - 1) ^ 2) := by norm_num
      _ = (256) * (x - 1) := by
        have h56 : (Real.sqrt (x - 1)) ^ 2 = x - 1 := by
          apply Real.sq_sqrt
          linarith
        rw [h56]
      _ = 256 * (x - 1) := by ring
  have h14 : x ^ 2 - 372 * x + 3620 = 0 := by
    nlinarith
  have h15 : (x - 10) * (x - 362) = 0 := by
    nlinarith [h14]
  cases' (mul_eq_zero.mp h15) with h16 h17
  · -- Case x - 10 = 0, so x = 10
    linarith
  · -- Case x - 362 = 0, so x = 362, check in original equation
    have h18 : x = 362 := by linarith
    have h19 : Real.sqrt (2 * x + 5) + Real.sqrt (x - 1) ≠ 8 := by
      rw [show x = 362 by linarith]
      have h20 : Real.sqrt (2 * (362 : ℝ) + 5) > 0 := by positivity
      have h21 : Real.sqrt ((362 : ℝ) - 1) > 0 := by positivity
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 * (362 : ℝ) + 5 by norm_num), 
                Real.sq_sqrt (show (0 : ℝ) ≤ (362 : ℝ) - 1 by norm_num), 
                Real.sqrt_nonneg (2 * (362 : ℝ) + 5), 
                Real.sqrt_nonneg (362 - 1 : ℝ)
               ]
    contradiction
  all_goals 
    try { tauto }
    <;> try { nlinarith }
  all_goals 
    try { tauto }
    <;> try { nlinarith }
  <;> try { contradiction }
  <;> try { linarith }
  <;> try { tauto }
  all_goals try { tauto } <;> try { nlinarith }
  <;> try { tauto }
  <;> try { tauto }
  <;> try { linarith }
  <;> try { tauto }
  <;> try { tauto }
  all_goals try { 
     tauto <;> try { nlinarith }
  }
  <;> try { tauto }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { tauto }
  <;> try { linarith }