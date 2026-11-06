import Mathlib

open Set Real

theorem algebra_328404 {a : ℝ} (ha : ∃! x : ℝ, 2^(1 + x) + 2^(1 - x) = a)
    (h : ∀ θ : ℝ, sin θ ∈ {x | 2^(1 + x) + 2^(1 - x) = a} → θ = 0 ∨ θ = π) :
    a = 4 := by

  rcases ha with ⟨x, hx1, hx2⟩
  have h_eq : (2 : ℝ) ^ (1 + (-x)) + (2 : ℝ) ^ (1 - (-x)) = a := by
    have eq1 : (2 : ℝ) ^ (1 + x) + (2 : ℝ) ^ (1 - x) = a := by 
      simpa using hx1
    have eq2 : (2 : ℝ) ^ (1 + (-x)) + (2 : ℝ) ^ (1 - (-x)) = (2 : ℝ) ^ (1 + x) + (2 : ℝ) ^ (1 - x) := by 
      have eq3 : (2 : ℝ) ^ (1 + (-x)) = (2 : ℝ) ^ (1 - x) := by 
        ring_nf
      have eq4 : (2 : ℝ) ^ (1 - (-x)) = (2 : ℝ) ^ (1 + x) := by 
        ring_nf
      rw [eq3, eq4]
      all_goals linarith 
    linarith [eq1, eq2]

  have eq2 : -x = x := by 
    have h3 : (2 : ℝ) ^ (1 + (-x)) + (2 : ℝ) ^ (1 - (-x)) = a := h_eq 
    have h4 : -x = x := by 
      apply hx2 (-x) 
      simpa using h_eq 
    linarith 

  have hx0 : x = 0 := by 
    linarith

  have ha4 : a = 4 := by 
    rw [hx0] at hx1 
    norm_num at hx1 ⊢ 
    linarith

  linarith [ha4]