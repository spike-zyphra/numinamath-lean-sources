import Mathlib

theorem algebra_97321 (a₁ a₂ : ℝ) (h_a_dist: a₁ ≠ a₂) (h : ∀ a:ℝ, (∃! x:ℝ, 4*x^2+a*x+8*x+9=0) ↔ (a = a₁ ∨ a = a₂)) : a₁ + a₂ = -16 := by 
  have h1 := h 4
  have h2 := h (-20)
  have h3 : (∃! x:ℝ, 4*x^2+4*x+8*x+9=0) := by
    use -3 / 2 
    constructor 
    · -- Show it is a solution
      norm_num 
    · -- Show it's unique 
      intro x h_eq 
      have h_eq : 4 * x ^ 2 + 4 * x + 8 * x + 9 = 0 := by linarith 
      have h : (2 * x + 3) ^ 2 = 0 := by 
        nlinarith 
      have h_eq2 : 2 * x + 3 = 0 := by 
        apply pow_eq_zero 
        exact h 
      linarith
  have h4 : (∃! x:ℝ, 4*x^2+(-20)*x+8*x+9=0) := by
    use 3 / 2 
    constructor 
    · -- Show it is a solution
      norm_num 
    · -- Show it's unique 
      intro x h_eq 
      have h_eq : 4 * x ^ 2 + (-20) * x + 8 * x + 9 = 0 := by linarith 
      have h : (2 * x - 3) ^ 2 = 0 := by 
        nlinarith 
      have h_eq2 : 2 * x - 3 = 0 := by 
        apply pow_eq_zero 
        exact h 
      linarith 
  have h5 : (4 = a₁ ∨ 4 = a₂) := by 
    specialize h1
    tauto 
  have h6 : (-20 = a₁ ∨ -20 = a₂) := by 
    specialize h2
    tauto 
  cases h5 with
  | inl h7 =>
    cases h6 with
    | inl h8 =>
      exfalso 
      linarith 
    | inr h9 =>
      linarith 
  | inr h8 =>
    cases h6 with
    | inl h9 =>
      linarith 
    | inr h10 =>
      exfalso 
      linarith