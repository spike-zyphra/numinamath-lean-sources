import Mathlib

theorem algebra_324686 {a b : ℝ} (ha : ∀ x ∈ Set.Icc 0 1, ∀ y ∈ Set.Icc 0 1, |a * x + b + a * y + b - x * y| ≤ 1 / 4) :
    a = 1 / 2 ∧ b = -1 / 8 := by
  have h1 := ha 0 (by norm_num) 0 (by norm_num)
  have h1' : |a * (0 : ℝ) + b + a * (0 : ℝ) + b - (0 : ℝ) * (0 : ℝ)| ≤ 1 / 4 := h1
  have h1_eq : a * (0 : ℝ) + b + a * (0 : ℝ) + b - (0 : ℝ) * (0 : ℝ) = 2 * b := by ring
  rw [h1_eq] at h1'
  have h2 := ha 1 (by norm_num) 1 (by norm_num)
  have h2' : |a * (1 : ℝ) + b + a * (1 : ℝ) + b - (1 : ℝ) * (1 : ℝ)| ≤ 1 / 4 := h2
  have h2_eq : a * (1 : ℝ) + b + a * (1 : ℝ) + b - (1 : ℝ) * (1 : ℝ) = 2 * a + 2 * b - 1 := by ring
  rw [h2_eq] at h2'
  have h3 := ha 0 (by norm_num) 1 (by norm_num)
  have h3' : |a * (0 : ℝ) + b + a * (1 : ℝ) + b - (0 : ℝ) * (1 : ℝ)| ≤ 1 / 4 := h3
  have h3_eq : a * (0 : ℝ) + b + a * (1 : ℝ) + b - (0 : ℝ) * (1 : ℝ) = a + 2 * b := by ring
  rw [h3_eq] at h3'
  have h4 := ha 1 (by norm_num) 0 (by norm_num)
  have h4' : |a * (1 : ℝ) + b + a * (0 : ℝ) + b - (1 : ℝ) * (0 : ℝ)| ≤ 1 / 4 := h4
  have h4_eq : a * (1 : ℝ) + b + a * (0 : ℝ) + b - (1 : ℝ) * (0 : ℝ) = 2 * b + a := by ring
  rw [h4_eq] at h4'
  have h11 : -1 / 4 ≤ 2 * b := by 
    cases' abs_le.mp h1' with h2 h3 
    linarith
  have h12 : 2 * b ≤ 1 / 4 := by 
    cases' abs_le.mp h1' with h2 h3 
    linarith
  -- From h1', we now will have upper and lower bounds for 2*b in context
  -- Now we can solve the system from goals
  have h21 : -1 / 4 ≤ 2 * a + 2 * b - 1 := by 
    cases' abs_le.mp h2' with h4 h5 
    linarith
  have h22 : 2 * a + 2 * b - 1 ≤ 1 / 4 := by 
    cases' abs_le.mp h2' with h4 h5 
    linarith
  -- From h2', we now have upper and lower bounds for expression 2*a+2*b-1
  -- Now we can solve the system from goals
  have h31 : -1 / 4 ≤ a + 2 * b := by 
    cases' abs_le.mp h3' with h6 h7 
    linarith
  have h32 : a + 2 * b ≤ 1 / 4 := by 
    cases' abs_le.mp h3' with h6 h7 
    linarith
  -- From h3', we now will have upper and lower bounds for a + 2*b
  have h5 : a = 1 / 2 := by
    linarith
  have h6 : b = -1 / 8 := by
    linarith
  exact ⟨h5, h6⟩