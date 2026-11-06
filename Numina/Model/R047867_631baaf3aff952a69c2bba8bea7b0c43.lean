import Mathlib

theorem algebra_157393 (m : ℝ) (M : Set ℝ) (hM : M = {x | m * x - 1 = 0}) :
    M ⊆ {x | x ^ 2 - 5 * x + 6 = 0} ↔ m = 1 / 2 ∨ m = 1 / 3 ∨ m = 0 := by 
  constructor
  · -- Forward (→): If M ⊆ {x | x^2 - 5*x + 6 = 0}, then m = 1/2 ∨ m = 1/3 ∨ m = 0
    intro h
    by_cases h1 : m = 0
    · 
      right
      right
      exact h1
    · 
      have h2 : m ≠ 0 := by
        intro h2
        contradiction 
      have h3 : ∀ (x : ℝ), m * x - 1 = 0 → x ^ 2 - 5 * x + 6 = 0 := by
        intro x hx
        have h4 : x ∈ M := by
          rw [hM]
          exact hx 
        have h5 : x ∈ {x : ℝ | x ^ 2 - 5 * x + 6 = 0} := h h4 
        exact h5 
      have h4 : m * (1 / m) - 1 = 0 := by
        field_simp [h2] 
      have h5 := h3 (1 / m) h4 
      have h6 : (1 / m) ^ 2 - 5 * (1 / m) + 6 = 0 := by 
        simpa using h5 
      have h7 : 6 * m ^ 2 - 5 * m + 1 = 0 := by 
        have h7 : m ≠ 0 := h2 
        field_simp at h6 
        nlinarith 
      have h7 : (3 * m - 1) * (2 * m - 1) = 0 := by
        linarith 
      cases' (mul_eq_zero.mp h7) with h7 h7 
      · 
        right 
        left 
        linarith 
      · 
        left 
        linarith 
  · -- Backward (←): If m = 1/2 ∨ m = 1/3 ∨ m = 0, then M ⊆ {x | x^2 - 5*x + 6 = 0}
    intro h
    rcases h with h1 | h2 | h3 
    · -- (→) if m =1/2 then ...
      rw [h1] at hM 
      intro x hx 
      rw [hM] at hx 
      have h4 : x = 2 := by
        have h5 : (1 / 2 : ℝ) * x - 1 = 0 := hx 
        linarith 
      rw [h4]
      norm_num 
    · -- if m =1/3 then ...
      rw [h2] at hM 
      intro x hx 
      rw [hM] at hx 
      have h4 : x = 3 := by 
        have h5 : (1 / 3 : ℝ) * x - 1 = 0 := hx 
        linarith 
      rw [h4] 
      norm_num 
    · -- if m =0 then ...
      have h3' : m = 0 := h3 
      rw [h3'] at hM 
      intro x hx
      rw [hM] at hx 
      norm_num at hx