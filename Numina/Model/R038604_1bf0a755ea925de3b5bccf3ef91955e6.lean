import Mathlib

theorem algebra_231594 :
  {(x₁, x₂, x₃) : ℝ × ℝ × ℝ | 2 * x₁^2 / (1 + x₁^2) = x₂ ∧ 2 * x₂^2 / (1 + x₂^2) = x₃ ∧ 2 * x₃^2 / (1 + x₃^2) = x₁} =
  {(0, 0, 0), (1, 1, 1)} := by
  ext ⟨x₁, x₂, x₃⟩ 
  simp 
  constructor 
  · -- Assume ⟨x₁, x₂, x₃⟩ in LHS
    rintro ⟨hx₁, hx₂, hx₃⟩ 
    have h1 : 1 + x₁^2 > 0 := by 
      nlinarith [sq_nonneg x₁]
    have h2 : 1 + x₂^2 > 0 := by 
      nlinarith [sq_nonneg x₂]
    have h3 : 1 + x₃^2 > 0 := by 
      nlinarith [sq_nonneg x₃]
    have eq1 : 2 * x₁^2 = x₂ * (1 + x₁^2) := by
      have h₁'1 : 1 + x₁^2 > 0 := by nlinarith [sq_nonneg x₁]
      field_simp [h₁'1] at hx₁
      nlinarith 
    have eq2 : 2 * x₂^2 = x₃ * (1 + x₂^2) := by
      have h₂'1 : 1 + x₂^2 > 0 := by nlinarith [sq_nonneg x₂]
      field_simp [h₂'1] at hx₂ 
      nlinarith 
    have eq3 : 2 * x₃^2 = x₁ * (1 + x₃^2) := by 
      have h₃'1 : 1 + x₃^2 > 0 := by nlinarith [sq_nonneg x₃]
      field_simp [h₃'1] at hx₃
      nlinarith 
    have h_nonneg₁ : 0 ≤ x₁ := by 
      nlinarith [sq_nonneg (x₁^2), sq_nonneg (x₂ ^ 2), sq_nonneg (x₃ ^ 2),
        sq_nonneg (x₁), sq_nonneg (x₂), sq_nonneg (x₃),
        mul_pos (show 0 < 1 + x₁^2 by nlinarith) (show 0 < 1 + x₂^2 by nlinarith),
        mul_pos (show 0 < 1 + x₂^2 by nlinarith) (show 0 < 1 + x₃^2 by nlinarith),
        mul_pos (show 0 < 1 + x₃^2 by nlinarith) (show 0 < 1 + x₁^2 by nlinarith)]
    have h_nonneg₂ : 0 ≤ x₂ := by 
      nlinarith [sq_nonneg (x₁^2), sq_nonneg (x₂ ^ 2), sq_nonneg (x₃ ^ 2),
        sq_nonneg (x₁), sq_nonneg (x₂), sq_nonneg (x₃),
        mul_pos (show 0 < 1 + x₁^2 by nlinarith) (show 0 < 1 + x₂^2 by nlinarith),
        mul_pos (show 0 < 1 + x₂^2 by nlinarith) (show 0 < 1 + x₃^2 by nlinarith),
        mul_pos (show 0 < 1 + x₃^2 by nlinarith) (show 0 < 1 + x₁^2 by nlinarith)]
    have h_nonneg₃ : 0 ≤ x₃ := by 
      nlinarith [sq_nonneg (x₁^2), sq_nonneg (x₂ ^ 2), sq_nonneg (x₃ ^ 2),
        sq_nonneg (x₁), sq_nonneg (x₂), sq_nonneg (x₃),
        mul_pos (show 0 < 1 + x₁^2 by nlinarith) (show 0 < 1 + x₂^2 by nlinarith),
        mul_pos (show 0 < 1 + x₂^2 by nlinarith) (show 0 < 1 + x₃^2 by nlinarith),
        mul_pos (show 0 < 1 + x₃^2 by nlinarith) (show 0 < 1 + x₁^2 by nlinarith)]
    have h10 : x₁ * (x₁ - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x₁ - 1), sq_nonneg (x₂ - 1), sq_nonneg (x₃ - 1),
        mul_nonneg (show 0 ≤ x₁ by linarith) (show 0 ≤ x₂ by linarith),
        mul_nonneg (show 0 ≤ x₂ by linarith) (show 0 ≤ x₃ by linarith),
        mul_nonneg (show 0 ≤ x₃ by linarith) (show 0 ≤ x₁ by linarith)
      ]
    cases' (mul_eq_zero.mp h10) with h11 h12 
    · -- When x₁ = 0 
      have h₁ : x₁ = 0 := by linarith 
      have h₂ : x₂ = 0 := by 
        rw [h₁] at eq1 
        nlinarith [sq_nonneg (x₁ ^ 2), sq_nonneg (x₂ ^ 2)] 
      have h₃ : x₃ = 0 := by 
        rw [h₂] at eq2 
        nlinarith [sq_nonneg (x₂ ^ 2), sq_nonneg (x₃ ^ 2)] 
      simp [h₁, h₂, h₃] 
      <;> tauto 
    · -- When (x₁ - 1) ^ 2 = 0 
      have h₁ : x₁ - 1 = 0 := by
        apply pow_eq_zero 
        exact h12 
      have h₁' : x₁ = 1 := by linarith 
      have h₂ : x₂ = 1 := by
        rw [h₁'] at eq1
        nlinarith [sq_nonneg (x₁ ^ 2), sq_nonneg (x₂ ^ 2)] 
      have h₃ : x₃ = 1 := by
        rw [h₂] at eq2
        nlinarith [sq_nonneg (x₂ ^ 2), sq_nonneg (x₃ ^ 2)] 
      simp [h₁', h₂, h₃] 
      <;> tauto 
  · -- Now prove RHS to LHS
    rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · constructor
      · norm_num 
      constructor
      · norm_num
      · norm_num 
    · constructor
      · norm_num 
      constructor
      · norm_num
      · norm_num