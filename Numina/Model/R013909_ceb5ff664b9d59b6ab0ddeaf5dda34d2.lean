import Mathlib

theorem algebra_251
    (a : ℝ)
    (ha : 0 < a ∧ a < 1) :
    Real.sqrt ((a^2) + (1 / a^2) - 2) / (1 + 1 / a) * (1 / (1 + a)) = (1 - a) / (1 + a) := by
  have h1 : 0 < a := ha.1
  have h2 : a < 1 := ha.2
  have h3 : a > 0 := by linarith
  have h4 : a < 1 := by linarith
  have h5 : Real.sqrt ((a^2) + (1 / a^2) - 2) = Real.sqrt ((a - 1 / a) ^ 2) := by 
    have h6 : (a ^ 2 : ℝ) + (1 / a ^ 2) - 2 = (a - 1 / a) ^ 2 := by 
      field_simp
      <;> ring_nf
    rw [h6]
  have h6 : Real.sqrt ((a - 1 / a) ^ 2) = (1 / a - a) := by 
    have h7 : (a : ℝ) - 1 / a < 0 := by 
      have h8 : 1 / a > 1 := by 
        have h9 : 0 < a := h1
        have h10 : a < 1 := h2
        have h11 : a > 0 := by linarith
        have h12 : 1 / a > 1 := by
          apply (lt_div_iff₀ (by linarith)).mpr
          nlinarith
        linarith
      nlinarith
      all_goals 
        try { nlinarith }
        all_goals try { tauto }
    have h8 : Real.sqrt ((a - 1 / a) ^ 2) = abs (a - 1 / a) := by 
      rw [Real.sqrt_sq_eq_abs]
    rw [h8]
    rw [abs_of_neg h7]
    all_goals 
      ring_nf 
      <;> field_simp
      <;> nlinarith
    all_goals try { linarith }
    all_goals try { nlinarith }
  rw [h5, h6]
  have h9 : (1 + 1 / a : ℝ) = (a + 1) / a := by 
    field_simp
    <;> ring_nf
  rw [h9]
  have h10 : (1 / a - a : ℝ) / ((a + 1) / a) = (1 - a ^ 2) / (a + 1) := by 
    field_simp [(show a ≠ 0 by nlinarith)]
    <;> ring_nf
    <;> field_simp [(show a ≠ 0 by nlinarith)]
    <;> nlinarith
    all_goals try { 
      field_simp [(show a ≠ 0 by nlinarith)]
      <;> nlinarith 
    }
  rw [h10]
  have h11 : ((1 - a ^ 2) / (a + 1) : ℝ) * (1 / (1 + a)) = (1 - a) / (1 + a) := by 
    have h14 : a + 1 ≠ 0 := by 
      nlinarith
    field_simp [(show a + 1 ≠ 0 by nlinarith), (show 1 + a ≠ 0 by nlinarith)]
    <;> ring_nf
    <;> nlinarith
  rw [h11]
  all_goals try { 
    field_simp [(show a ≠ 0 by nlinarith), (show 1 + a ≠ 0 by nlinarith)]
    <;> nlinarith 
    <;> positivity
  }
  all_goals try { 
    positivity
    <;> tauto
    <;> try { field_simp [(show a ≠ 0 by nlinarith), (show 1 + a ≠ 0 by nlinarith)] }
    <;> nlinarith 
  }
  all_goals try { 
    field_simp [(show a ≠ 0 by nlinarith), (show 1 + a ≠ 0 by nlinarith)]
    <;> positivity
    <;> nlinarith 
    <;> try { tauto }
  }
  all_goals try { 
    field_simp [(show a > 0 by linarith), (show a < 1 by linarith), (show 1 > 0 by norm_num ), (show a + 1 ≠ 0 by nlinarith)
      ]
    <;> nlinarith <;> positivity
    <;> nlinarith
    <;> positivity
    <;> tauto
  }
  all_goals try { linarith }
  <;> nlinarith
  <;> positivity
  <;> tauto