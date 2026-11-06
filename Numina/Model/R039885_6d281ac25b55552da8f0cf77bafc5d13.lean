import Mathlib

theorem algebra_10207 {x : ℝ} (hx : x > 0) (h : x * ⌊x⌋ = 70) :
    x = 8.75 := by
  have h1 : ⌊x⌋ ≤ (x : ℝ) := by 
    exact Int.floor_le x
  have h2 : (x : ℝ) < (⌊x⌋ + 1 : ℝ) := by 
    exact Int.lt_floor_add_one x
  have h5 : ⌊x⌋ ≥ 1 := by
    by_contra h6 
    push_neg at h6 
    have h6' : ⌊x⌋ ≤ 0 := by 
      omega
    have h7 : ⌊x⌋ = 0 ∨ ⌊x⌋ < 0 := by 
      omega
    rcases h7 with (h8 | h9)
    · 
      have h10 : ⌊x⌋ = 0 := h8
      have h11 : (⌊x⌋ : ℝ) = (0 : ℝ) := by 
        exact_mod_cast h10
      rw [h11] at h 
      nlinarith
    · 
      have h10 : ⌊x⌋ < (0 : ℤ) := by 
        omega
      have h11 : (⌊x⌋ : ℝ) < (0 : ℝ) := by 
        exact_mod_cast h10
      nlinarith [h11, h, hx]
  have h8 : ⌊x⌋ ≤ 8 := by 
    by_contra h9 
    push_neg at h9 
    have h9' : ⌊x⌋ ≥ 9 := by 
      omega
    have h9'' : (⌊x⌋ : ℝ) ≥ (9 : ℝ) := by 
      exact_mod_cast h9'
    nlinarith [h1, h, h9'', h2]
  have h9 : ⌊x⌋ ≥ 8 := by 
    by_contra h10 
    push_neg at h10 
    have h10' : ⌊x⌋ ≤ 7 := by 
      omega
    have h10'' : (⌊x⌋ : ℝ) ≤ (7 : ℝ) := by 
      exact_mod_cast h10'
    nlinarith [h1, h, h10'', h2]
  have h10 : ⌊x⌋ = 8 := by 
    omega
  have h11 : (⌊x⌋ : ℝ) = (8 : ℝ) := by 
    exact_mod_cast h10 
  rw [h11] at h 
  have h12 : x = (8.75 : ℝ) := by 
    nlinarith
  linarith