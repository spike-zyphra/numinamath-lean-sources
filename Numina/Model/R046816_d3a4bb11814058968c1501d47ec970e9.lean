import Mathlib

theorem algebra_201611 (α β : ℝ) (h : α ≠ β) (h₁ : α^2 - 6 * α + 5 = 0) (h₂ : β^2 - 6 * β + 5 = 0)
    (f : ℝ → ℝ) (hf : f = fun x => abs (x - α) + abs (x - β)) :
    IsLeast {x | ∃ y, x = f y} 4 := by
  
  have h₃ : (α - 1) * (α - 5) = 0 := by
    linarith
  
  have h₄ : α = 1 ∨ α = 5 := by 
    cases (mul_eq_zero.mp h₃) with
    | inl h₅ => 
      left
      linarith 
    | inr h₆ => 
      right
      linarith
  
  have h₅ : (β - 1) * (β - 5) = 0 := by
    linarith
  
  have h₆ : β = 1 ∨ β = 5 := by
    cases (mul_eq_zero.mp h₅) with
    | inl h₇ => 
      left
      linarith 
    | inr h₈ => 
      right
      linarith
  
  have h₇ : (α = 1 ∧ β = 5) ∨ (α = 5 ∧ β = 1) := by
    cases h₄ with
    | inl h₈ => 
      cases h₆ with
      | inl h₉ => 
        exfalso
        apply h
        linarith
      | inr h₉ => 
        left
        constructor <;> linarith
    | inr h₈ => 
      cases h₆ with
      | inl h₉ => 
        right
        constructor <;> linarith
      | inr h₉ => 
        exfalso
        apply h
        linarith
  
  rcases h₇ with ⟨hα, hβ⟩ | ⟨hα, hβ⟩
  · 
    -- Assume α = 1, β = 5
    have hfα : f = fun x => abs (x - 1) + abs (x - 5) := by 
      rw [hf]
      funext x
      simp [hα, hβ]
  
    constructor
    · -- Show 4 is in the image 
      use 3 
      rw [hfα]
      norm_num [abs_of_neg, abs_of_pos, sub_eq_add_neg]
      <;> try { tauto }
  
    · -- Show it is minimal 
      intro x hx
      rcases hx with ⟨y, hy⟩
      rw [hfα] at hy 
      simp at hy
      have h : abs (y - 1) + abs (y - 5) ≥ 4 := by 
        have h₈ : abs (y - 1) + abs (y - 5) ≥ abs ((y - 1) - (y - 5)) := by 
          apply abs_sub 
        have h₉ : abs ((y - 1) - (y - 5)) = 4 := by 
          have h : (y - 1 : ℝ) - (y - 5 : ℝ) = 4 := by 
            linarith 
          rw [h] 
          norm_num 
        linarith [h₈, h₉]
  
      linarith 
  · -- Assume α = 5, β = 1
    have hfα : f = fun x => abs (x - 5) + abs (x - 1) := by 
      rw [hf]
      funext x 
      simp [hα, hβ]
  
    constructor
    · -- Show 4 is in the image 
      use 3 
      rw [hfα]
      norm_num [abs_of_neg, abs_of_pos, sub_eq_add_neg]
      <;> try { tauto }
  
    · -- Show it is minimal 
      intro x hx
      rcases hx with ⟨y, hy⟩
      rw [hfα] at hy 
      simp at hy 
      have h : abs (y - 5) + abs (y - 1) ≥ 4 := by 
        have h₈ : abs (y - 5) + abs (y - 1) ≥ abs ((y - 5) - (y - 1)) := by 
          apply abs_sub 
        have h₉ : abs ((y - 5) - (y - 1)) = 4 := by 
          have h : (y - 5 : ℝ) - (y - 1 : ℝ) = -4 := by 
            linarith 
          rw [h] 
          norm_num 
        linarith [h₈, h₉]
  
      linarith