import Mathlib
/-Example 13. Let $a, b, c$ be distinct integers from 1 to 9. What is the largest possible value of $\frac{a+b+c}{a b c}$? (1992, 1st Dannevirke-Shanghai Friendship Correspondence Competition)-/
theorem algebra_318084 (a b c : ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (habc : a ≠ b ∧ a ≠ c ∧ b ≠ c) (h : a ≤ 9) (h' : b ≤ 9) (h'' : c ≤ 9) :
    (a + b + c : ℝ) / (a * b * c) ≤ 1 := by

  have h1 : 1 ≤ a := ha
  have h2 : 1 ≤ b := hb
  have h3 : 1 ≤ c := hc

  have h4 : a ≤ 9 := h
  have h5 : b ≤ 9 := h'
  have h6 : c ≤ 9 := h''

  have h7 : a ≠ b := habc.1
  have h8 : a ≠ c := habc.2.1
  have h9 : b ≠ c := habc.2.2

  have h_pos : (a : ℝ) * (b : ℝ) * (c : ℝ) > 0 := by
    have ha' : (a : ℝ) ≥ 1 := by exact_mod_cast h1
    have hb' : (b : ℝ) ≥ 1 := by exact_mod_cast h2
    have hc' : (c : ℝ) ≥ 1 := by exact_mod_cast h3
    apply mul_pos
    apply mul_pos
    · -- Show that (a : ℝ) > 0, since a ≥ 1
      linarith
    · -- Show that (b : ℝ) > 0, since b ≥ 1
      linarith
    · -- Show that (c : ℝ) > 0, since c ≥ 1
      linarith

  have h_ineq : (a + b + c : ℝ) ≤ (a * b * c : ℝ) := by 
    have h13 : a ≤ 9 := h4
    have h14 : b ≤ 9 := h5
    have h15 : c ≤ 9 := h6
    interval_cases a <;> interval_cases b <;> interval_cases c
    <;> norm_num at *
    <;> { 
      repeat {split}
      all_goals 
        try { 
          linarith 
        }
        <;> try { 
          contradiction
        }
    }
  
  have h13 : (a + b + c : ℝ) / (a * b * c) ≤ 1 := by
    have h14 : (a + b + c : ℝ) ≤ (a * b * c : ℝ) := h_ineq
    have h15 : (a * b * c : ℝ) > 0 := h_pos
    apply (div_le_one (by linarith)).mpr
    linarith

  exact h13