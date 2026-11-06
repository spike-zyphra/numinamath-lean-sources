import Mathlib

theorem number_theory_316489 (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h1 : 56 ≤ a + b) (h2 : a + b ≤ 59) (h3 : 0.9 < (a : ℝ) / b ∧ (a : ℝ) / b < 0.91) :
    b^2 - a^2 = 177 := by

  have h4 : (a : ℝ) / b > 0.9 := by linarith [h3.1]
  have h5 : (a : ℝ) / b < 0.91 := by linarith [h3.2]

  have h6 : 9 * (b : ℝ) < 10 * (a : ℝ) := by
    have h7 : (a : ℝ) / (b : ℝ) > 0.9 := h4 
    apply (lt_div_iff₀ (by positivity)).mp at h7
    linarith

  have h6' : 9 * b < 10 * a := by
    have h7 : (9 * (b : ℝ) < 10 * (a : ℝ)) := h6
    exact_mod_cast h7

  have h7 : 100 * (a : ℝ) < 91 * (b : ℝ) := by
    have h8 : (a : ℝ) / (b : ℝ) < 0.91 := h5
    apply (div_lt_iff₀ (by positivity)).mp at h8 
    linarith

  have h7' : 100 * a < 91 * b := by 
    have h8 : (100 * (a : ℝ) < 91 * (b : ℝ)) := h7
    exact_mod_cast h8

  have h8 : a ≤ 59 := by omega 
  have h9 : b ≤ 59 := by omega 

  interval_cases a <;> try { 
    omega
  } <;> interval_cases b <;> norm_num at h6' h7' h1 h2 
    <;> omega