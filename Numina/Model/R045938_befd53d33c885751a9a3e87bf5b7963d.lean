import Mathlib

theorem algebra_279067 :
  {x : ℝ | ∃ c₁ c₂ c₃ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧ c₃ > 0 ∧ 
    5/c₁ + 5/c₂ = 15 ∧ 5/c₂ + 5/c₃ = 11 ∧ 
    x/c₁ = 10/c₂ + (10+x)/c₃ ∧ x > 0} = 
  {27.5} := by
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor 
  · -- Assume x ∈ { ..., | conditions }, prove x = 27.5
    rintro ⟨c₁, c₂, c₃, hc₁, hc₂, hc₃, heq1, heq2, heq3, hx⟩
    have eq1 : c₁ + c₂ = 3 * c₁ * c₂ := by 
      field_simp [(show c₁ ≠ 0 by linarith), (show c₂ ≠ 0 by linarith)] at heq1 ⊢
      nlinarith
    have eq2 : c₃ + c₂ = 11 / 5 * (c₂ * c₃) := by
      field_simp [(show c₂ ≠ 0 by linarith), (show c₃ ≠ 0 by linarith)] at heq2 ⊢
      nlinarith 
    have eq3 : x * (c₂ * c₃) = (10 * c₃ + (10 + x) * c₂) * c₁ := by 
      field_simp [(show c₁ ≠ 0 by linarith), (show c₂ ≠ 0 by linarith), 
          (show c₃ ≠ 0 by linarith)] at heq3 ⊢
      nlinarith
    have h1 : x = 27.5 := by 
      nlinarith [sq_pos_of_pos hc₁, sq_pos_of_pos hc₂, sq_pos_of_pos hc₃, 
          sq_nonneg (c₁ - c₂), sq_nonneg (c₃ - c₂), sq_nonneg (c₁ - c₃), 
          mul_pos hc₁ hc₂, mul_pos hc₂ hc₃, mul_pos hc₁ hc₃, mul_pos hc₁ (show 0 < (x : ℝ) by linarith), mul_pos hc₂ (show 0 < (x : ℝ) by linarith)]
    linarith
  · -- Assume x = 27.5, prove ⟨c₁, c₂, c₃, hc₁, hc₂, hc₃, heq1, heq2, heq3, hx⟩ 
    intro heq
    rw [heq] 
    use 1, 1 / 2, 5 
    constructor 
    · norm_num 
    constructor
    · norm_num 
    constructor
    · norm_num 
    constructor 
    · norm_num 
    constructor
    · norm_num 
    constructor 
    · norm_num 
    all_goals norm_num