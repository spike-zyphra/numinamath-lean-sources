import Mathlib

theorem algebra_308134 {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h1 : 56 ≤ a + b) (h2 : a + b ≤ 59) (h3 : 0.9 < (a / b : ℝ)) (h4 : (a / b : ℝ) < 0.91) :
    b^2 - a^2 = 177 := by
  have h5 : (a : ℝ) > 0 := by
    exact_mod_cast (show (0 : ℕ) < a by linarith)
  have h6 : (b : ℝ) > 0 := by
    exact_mod_cast (show (0 : ℕ) < b by linarith)
  have h7 : 10 * (a : ℝ) > 9 * (b : ℝ) := by
    have h8 : (a / b : ℝ) > 0.9 := by linarith
    have h9 : (a : ℝ) / (b : ℝ) > 0.9 := by linarith
    have h10 : (a : ℝ) > 0.9 * (b : ℝ) := by
      have h11 : (b : ℝ) > 0 := h6
      apply (lt_div_iff₀ h11).mp at h9
      linarith
    nlinarith
  have h8 : 10 * a > 9 * b := by
    exact_mod_cast (show 10 * (a : ℝ) > 9 * (b : ℝ) by linarith [h7])
  have h11 : (100 : ℝ) * (a : ℝ) < 91 * (b : ℝ) := by
    have h12 : (a / b : ℝ) < 0.91 := by linarith
    have h13 : (a : ℝ) / (b : ℝ) < 0.91 := by linarith
    have h14 : (a : ℝ) < 0.91 * (b : ℝ) := by
      have h11 : (b : ℝ) > 0 := h6
      apply (div_lt_iff₀ h11).mp at h13
      linarith
    nlinarith
  have h12 : 100 * a < 91 * b := by
    exact_mod_cast (show (100 : ℝ) * (a : ℝ) < 91 * (b : ℝ) by linarith [h11])
  have h13 : a ≤ 58 := by
    omega
  have h14 : b ≤ 58 := by 
    omega
  interval_cases a <;> try { 
    omega 
  } <;> try { 
    interval_cases b <;> norm_num at h8 h12 h1 h2 
    <;> all_goals 
      try { 
        omega 
      } 
    <;> try { 
      all_goals 
        native_decide 
    }
  }