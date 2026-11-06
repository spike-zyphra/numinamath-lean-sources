import Mathlib

theorem algebra_187091 (x y : ℝ) (h₀ : x ^ 4 + y ^ 4 = 82) (h₁ : x * y = 3) :
    (x = 1 ∧ y = 3) ∨ (x = 3 ∧ y = 1) ∨ (x = -1 ∧ y = -3) ∨ (x = -3 ∧ y = -1) := by
  have h2 : x ^ 2 * y ^ 2 = 9 := by
    nlinarith [sq_nonneg (x * y - 3), sq_nonneg (x ^ 2 - y ^ 2)]
  have h3 : (x ^ 2 + y ^ 2) ^ 2 = 100 := by 
    nlinarith [sq_nonneg (x ^ 2 - y^2), h₀, h2]
  have h4 : x ^ 2 + y ^ 2 = 10 := by 
    nlinarith [sq_nonneg (x ^ 2 - y^2), sq_nonneg (x^2 + y^2)]
  have h5 : (x + y)^2 = 16 := by 
    nlinarith [h₁, h4]
  have h6 : x + y = 4 ∨ x + y = -4 := by
    have h7 : (x + y)^2 - 16 = 0 := by linarith 
    have h8 : ((x + y) - 4) * ((x + y) + 4) = 0 := by
      nlinarith 
    cases mul_eq_zero.1 h8 with
    | inl h9 => 
      left
      nlinarith 
    | inr h10 => 
      right
      nlinarith 
  cases h6 with
  | inl h6 => 
    have h7 : x + y = 4 := h6
    have h8 : (x - 1) * (x - 3) = 0 := by 
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 4), sq_nonneg (x * y - 3), sq_nonneg (x - 1), sq_nonneg (x - 3), sq_nonneg (y - 1), sq_nonneg (y - 3)] 
    cases mul_eq_zero.1 h8 with
    | inl hx1 => 
      have hx1 : x = 1 := by linarith
      have hy1 : y = 3 := by nlinarith 
      left 
      exact ⟨hx1, hy1⟩ 
    | inr hx3 => 
      have hx3 : x = 3 := by linarith
      have hy3 : y = 1 := by nlinarith 
      right 
      left 
      exact ⟨hx3, hy3⟩ 
  | inr h6 => 
    have h7 : x + y = -4 := h6
    have h8 : (x + 1) * (x + 3) = 0 := by 
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y + 4), sq_nonneg (x * y - 3), sq_nonneg (x + 1), sq_nonneg (x + 3), sq_nonneg (y + 1), sq_nonneg (y + 3)]
    cases mul_eq_zero.1 h8 with
    | inl hx1 => 
      have hx1 : x = -1 := by linarith
      have hy1 : y = -3 := by nlinarith 
      simp [hx1, hy1]
      <;> tauto 
    | inr hx3 => 
      have hx3 : x = -3 := by linarith
      have hy3 : y = -1 := by nlinarith 
      simp [hx3, hy3]
      <;> tauto 
  all_goals 
    nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 3), sq_nonneg (x + 1), sq_nonneg (x + 3)]
  <;> tauto 
  <;> nlinarith
  all_goals 
    try { 
      tauto 
      <;> nlinarith 
      <;> try { 
        tauto 
      }
    }
  all_goals 
    tauto
  <;> try { 
    contradiction 
    <;> try { 
      nlinarith 
      all_goals tauto 
    }
  }
  all_goals 
    tauto 
    <;> try { 
      tauto 
    }
  all_goals 
    contradiction