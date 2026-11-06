import Mathlib

theorem algebra_41595 :
  {x | x + 1 ≠ 0 ∧ x + 2 ≠ 0 ∧ x ≠ 0 ∧ 1 / (x + 1) + 1 / (x + 2) = 1 / x} = {√2, -√2} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    and_imp]
  constructor
  · -- Assume x is in the left side
    intro h
    rcases h with ⟨h1, h2, h3, heq⟩
    have eq1 : x ≠ 0 := h3
    have eq2 : x + 1 ≠ 0 := h1
    have eq3 : x + 2 ≠ 0 := h2
    field_simp [(show x + 1 ≠ 0 by exact h1), (show x + 2 ≠ 0 by exact h2),
        (show x ≠ 0 by exact h3)] at heq
    have h4 : x ^ 2 = 2 := by 
      nlinarith 
    have h5 : x = Real.sqrt 2 ∨ x = -Real.sqrt 2 := by 
      have h6 : x ^ 2 = (2 : ℝ) := h4
      have : x = Real.sqrt 2 ∨ x = -Real.sqrt 2 := by
        have h7 : x ^ 2 - (2 : ℝ) = 0 := by linarith
        have h8 : (x - Real.sqrt 2) * (x + Real.sqrt 2) = 0 := by
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
        cases' (mul_eq_zero.1 h8) with h9 h10
        · -- x - Real.sqrt 2 = 0 
          left 
          linarith 
        · -- x + Real.sqrt 2 = 0 
          right 
          nlinarith 
      tauto 
    tauto 
  · -- Now the reverse direction
    rintro (rfl | rfl)
    · -- Assume x = Real.sqrt 2 
      have h1 : Real.sqrt 2 + 1 ≠ 0 := by 
        have h_pos : 0 < Real.sqrt 2 := by
          apply Real.sqrt_pos.2
          all_goals linarith
        linarith 
      have h2 : Real.sqrt 2 + 2 ≠ 0 := by 
        have h_pos : 0 < Real.sqrt 2 := by
          apply Real.sqrt_pos.2
          all_goals linarith
        linarith 
      have h3 : Real.sqrt 2 ≠ 0 := by 
        have h_pos : 0 < Real.sqrt 2 := by
          apply Real.sqrt_pos.2
          all_goals linarith
        linarith 
      constructor 
      · exact h1 
      constructor
      · exact h2 
      constructor
      · exact h3 
      · -- Show that sqrt 2 satisfies the equation 
        field_simp [h1, h2, h3] 
        <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    · -- Assume x = -Real.sqrt 2 
      have h1 : -Real.sqrt 2 + 1 ≠ 0 := by 
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      have h2 : -Real.sqrt 2 + 2 ≠ 0 := by 
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      have h3 : -Real.sqrt 2 ≠ 0 := by 
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      constructor
      · exact h1
      constructor
      · exact h2
      constructor
      · exact h3 
      · -- Show that -sqrt 2 satisfies the equation 
        field_simp [h1, h2, h3]
        <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]