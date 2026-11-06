import Mathlib

theorem number_theory_84151 (a b c : ℚ) (_ : 0 < a) (h₀ : 0 < b) (h₁ : 0 < c)
    (h₂ : Real.sqrt a + Real.sqrt b = c) :
    ∃ q₁ q₂ : ℚ, Real.sqrt a = q₁ ∧ Real.sqrt b = q₂ := by

  have h3 : Real.sqrt a ≥ 0 := by
    apply Real.sqrt_nonneg

  have h4 : Real.sqrt b ≥ 0 := by
    apply Real.sqrt_nonneg
  
  have h5 : (Real.sqrt a + Real.sqrt b : ℝ) = (c : ℝ) := by
    exact_mod_cast h₂
  
  have h6 : Real.sqrt b = (c : ℝ) - Real.sqrt a := by 
    linarith
  
  have h10 : (Real.sqrt a : ℝ) ^ 2 = (a : ℝ) := by
    rw [Real.sq_sqrt]
    exact_mod_cast (show (0 : ℚ) ≤ a by linarith)

  have h8 : (Real.sqrt b : ℝ) ^ 2 = (b : ℝ) := by 
    rw [Real.sq_sqrt]
    exact_mod_cast h₀.le
  
  have h9 : ( (c : ℝ) - Real.sqrt a ) ^ 2 = (b : ℝ) := by
    rw [show ( (c : ℝ) - Real.sqrt a ) = Real.sqrt b by linarith [h6] ]
    linarith
  
  have h11 : 2 * (c : ℝ) * (Real.sqrt a : ℝ) = (c : ℝ) ^ 2 + (a : ℝ) - (b : ℝ) := by
    nlinarith [h9, h10]

  have h12 : (Real.sqrt a : ℝ) = ((c ^ 2 + a - b) / (2 * c) : ℚ) := by 
    have h14 : (c : ℝ) ≠ 0 := by
      positivity
    field_simp at *
    nlinarith
  
  have h13 : (Real.sqrt b : ℝ) = ((c ^ 2 + b - a) / (2 * c) : ℚ) := by
    have h6' : Real.sqrt b = (c : ℝ) - Real.sqrt a := by 
      linarith 
    rw [h6']
    rw [h12]
    field_simp at *
    <;> nlinarith
  
  refine' ⟨(c ^ 2 + a - b) / (2 * c), (c ^ 2 + b - a) / (2 * c), ?_, ?_⟩

  all_goals
    try { 
      exact_mod_cast (show (Real.sqrt a : ℝ) = ((c ^ 2 + a - b) / (2 * c) : ℚ) by linarith [h12])
    }
    try { 
      exact_mod_cast (show (Real.sqrt b : ℝ) = ((c ^ 2 + b - a) / (2 * c) : ℚ) by linarith [h13])
    }