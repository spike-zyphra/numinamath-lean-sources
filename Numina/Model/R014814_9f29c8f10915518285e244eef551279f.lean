import Mathlib

theorem algebra_172009 (a b : ℝ) (h₀ : a ≠ 0) (h₁ : b ≠ 0)
    (h₂ : {x | x = b ∨ x = b / a ∨ x = 0} = {x | x = a ∨ x = a + b ∨ x = 1}) :
    a ^ 2018 + b ^ 2018 = 2 := by 
  have h3 : (0 : ℝ) ∈ {x | x = a ∨ x = a + b ∨ x = 1} := by 
    have h3 : (0 : ℝ) ∈ {x | x = b ∨ x = b / a ∨ x = 0} := by 
      simp 
    rw [h₂] at h3
    exact h3 
  have h4 : (0 = a ∨ 0 = a + b ∨ (0 : ℝ) = 1) := by 
    simpa using h3 
  cases h4 with 
  | inl h4 => 
    exfalso 
    apply h₀ 
    linarith 
  | inr h4 => 
    cases h4 with 
    | inl h4 => -- 0 = a + b
      have h5 : (1 : ℝ) ∈ {x | x = b ∨ x = b / a ∨ x = 0} := by 
        rw [h₂]
        simp 
      have h6 : (1 = b ∨ 1 = b / a ∨ (1 : ℝ) = 0) := by 
        simpa using h5 
      rcases h6 with (h7 | h7 | h7)
      · -- 1 = b. So b = 1
        have h8 : a = -1 := by
          linarith [h4, h7]
        have h9 : b = (1 : ℝ) := by
          linarith [h7]
        norm_num [h8, h9]
      · -- 1 = b / a
        have h10 : b = a := by
          field_simp [h₀] at h7 
          linarith 
        have h11 : a = (0 : ℝ) := by
          linarith [h10, h4]
        exfalso 
        apply h₀ 
        linarith
      · -- (1 : ℝ) = 0
        exfalso 
        linarith
    | inr h4 => 
      exfalso 
      linarith