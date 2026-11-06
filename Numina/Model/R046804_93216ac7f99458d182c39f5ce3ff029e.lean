import Mathlib
theorem algebra_318084 (a b c : ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (habc : a ≠ b ∧ a ≠ c ∧ b ≠ c) (h : a ≤ 9) (h' : b ≤ 9) (h'' : c ≤ 9) :
    (a + b + c : ℝ) / (a * b * c) ≤ 1 := by
  have hab' : a ≠ b := habc.1
  have hac' : a ≠ c := habc.2.1
  have hbc' : b ≠ c := habc.2.2

  have h11 : a * b * c ≥ a + b + c := by 
    interval_cases a <;> interval_cases b <;> interval_cases c <;> norm_num 
      <;> norm_num [hab', hac', hbc'] 
      <;> tauto 
  have h7 : (a * b * c : ℝ) ≥ (a + b + c : ℝ) := by 
    have h8 : (a * b * c : ℝ) ≥ (a + b + c : ℝ) := by
      exact_mod_cast h11 
    linarith 
  have h8 : 0 < (a * b * c : ℝ) := by 
    have ha' : (a : ℝ) ≥ 1 := by exact_mod_cast (show 1 ≤ a by linarith)
    have hb' : (b : ℝ) ≥ 1 := by exact_mod_cast (show 1 ≤ b by linarith)
    have hc' : (c : ℝ) ≥ 1 := by exact_mod_cast (show 1 ≤ c by linarith)
    positivity 
  have h9 : (a + b + c : ℝ) / (a * b * c) ≤ 1 := by 
    have h10 : (a * b * c : ℝ) ≥ (a + b + c : ℝ) := h7 
    have h11 : 0 < (a * b * c : ℝ) := h8 
    apply (div_le_iff₀ (by linarith)).mpr 
    linarith 
  exact h9