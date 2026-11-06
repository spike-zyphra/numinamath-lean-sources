import Mathlib

theorem algebra_327833 {α β : ℝ} (h₁ : α^2 - α - 2006 = 0) (h₂ : β^2 - β - 2006 = 0)
    (h₃ : α ≠ β) :
    α + 2006 / (1 + 2006 / (1 + 2006 / β)) = 0 := by
  have h4 : α + β = 1 := by
    have h5 : α^2 - β^2 = α - β := by linarith [h₁, h₂]
    have h6 : (α - β) * (α + β - 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h6) with h7 h8
    · 
      exfalso
      have h7' : α = β := by
        linarith
      tauto
    · 
      linarith
  
  have h5 : β ≠ 0 := by
    by_contra h
    rw [h] at h₂
    nlinarith
  
  have h6 : 1 + 2006 / β = β := by
    have h7 : β^2 = β + 2006 := by linarith [h₂]
    have h8 : β + 2006 = β^2 := by linarith
    have h9 : 1 + 2006 / β = β := by
      field_simp [h5] at *
      <;> nlinarith
    exact h9
  
  have h7 : 1 + 2006 / (1 + 2006 / β) = β := by
    rw [h6]
    all_goals linarith
  
  have h8 : 2006 / β = β - 1 := by
    have h7 : β^2 = β + 2006 := by linarith [h₂]
    have h5 : β ≠ 0 := h5
    field_simp [h5] at *
    <;> nlinarith
  
  rw [h7]
  rw [h8]
  linarith [h4]
  all_goals nlinarith
  <;> tauto
  <;> norm_num
  <;> tauto
  all_goals nlinarith [h4]
  <;> tauto
  <;> try { norm_num at * }
  <;> try { tauto }
  all_goals linarith [h4, h5, h6, h7, h8]