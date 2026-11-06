import Mathlib

theorem algebra_120346 {a b c : ℚ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : Real.sqrt a + Real.sqrt b = c) :
    ∃ q1 q2 : ℚ, q1 = Real.sqrt a ∧ q2 = Real.sqrt b := by
  have ha1 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb1 : (0 : ℝ) < b := by exact_mod_cast hb
  have hc1 : (0 : ℝ) < c := by exact_mod_cast hc
  have h2 : Real.sqrt a = c - Real.sqrt b := by 
    linarith 
  have h4 : (Real.sqrt a) ^ 2 = (a : ℝ) := Real.sq_sqrt (by
    exact_mod_cast show 0 ≤ a by linarith
    )
  have h3 : (c - Real.sqrt b) ^ 2 = (a : ℝ) := by
    have h2' : Real.sqrt a = c - Real.sqrt b := h2
    rw [←h2'] 
    all_goals 
      nlinarith [Real.sqrt_nonneg (a : ℝ), Real.sqrt_nonneg (b : ℝ)]
  have h6 : (Real.sqrt b : ℝ) ^ 2 = (b : ℝ) := Real.sq_sqrt (by
    exact_mod_cast show 0 ≤ b by linarith
    )
  have h7 : (c : ℝ) ^ 2 - 2 * (c : ℝ) * (Real.sqrt b : ℝ) + (b : ℝ) = (a : ℝ) := by 
    nlinarith [h3, h6]
  have h8 : (Real.sqrt b : ℝ) = ((c^2 + b - a) / (2 * c) : ℚ) := by
    have h9 : (c : ℝ) ^ 2 - 2 * (c : ℝ) * (Real.sqrt b : ℝ) + (b : ℝ) = (a : ℝ) := h7
    field_simp at *
    linarith 
    <;> norm_num 
    all_goals nlinarith 
  have h9 : (Real.sqrt a : ℝ) = ((c^2 + a - b) / (2 * c) : ℚ) := by 
    have h2' : (Real.sqrt a : ℝ) = c - (Real.sqrt b : ℝ) := h2
    rw [h2']
    rw [h8]
    field_simp at *
    <;> nlinarith 
    <;> norm_num 
  use ( (c^2 + a - b) / (2 * c) : ℚ )
  use ( (c^2 + b - a) / (2 * c) : ℚ )
  constructor 
  · -- Show q1 = Real.sqrt a 
    have h10 : (Real.sqrt a : ℝ) = (↑((c^2 + a - b) / (2 * c) : ℚ) : ℝ) := by 
      exact_mod_cast h9 
    linarith [h10] 
  · -- Show q2 = Real.sqrt b 
    have h11 : (Real.sqrt b : ℝ) = (↑((c^2 + b - a) / (2 * c) : ℚ) : ℝ) := by 
      exact_mod_cast h8 
    linarith [h11] 
  all_goals try { norm_num } <;> try { linarith }
  <;> try { norm_num <;> linarith }
  <;> try { tauto } <;> try { nlinarith }