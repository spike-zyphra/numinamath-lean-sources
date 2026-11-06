import Mathlib

theorem number_theory_251675 (x y z : ℕ) (h₀ : x < y) (h₁ : y < z)
    (h₂ : 3^x + 3^y + 3^z = 21897) :
    (x, y, z) = (3, 7, 9) := by

  have h3 : x ≤ 9 := by
    by_contra h
    push_neg at h 
    have h4 : 3^x ≥ 3^10 := by 
      have : x ≥ 10 := by omega 
      exact Nat.pow_le_pow_of_le_right (by norm_num) this 
    have h5 : 3^x + 3^y + 3^z ≥ 3^x := by 
      linarith [show 0 ≤ (3^y : ℕ) by positivity, show 0 ≤ (3^z : ℕ) by positivity]
    have h6 : 3^x ≤ 21897 := by 
      linarith [h₂, h5]
    norm_num at h4 h6 
    all_goals linarith

  have h4 : y ≤ 9 := by
    by_contra h 
    push_neg at h 
    have h5 : 3^y ≥ 3^10 := by 
      have : y ≥ 10 := by omega 
      exact Nat.pow_le_pow_of_le_right (by norm_num) this 
    have h6 : 3^x + 3^y + 3^z ≥ 3^y := by 
      linarith [show 0 ≤ (3^x : ℕ) by positivity, show 0 ≤ (3^z : ℕ) by positivity]
    have h7 : 3^y ≤ 21897 := by 
      linarith [h₂, h6]
    norm_num at h5 h7 
    all_goals linarith

  have h5 : z ≤ 9 := by 
    by_contra h 
    push_neg at h 
    have h6 : 3^z ≥ 3^10 := by 
      have : z ≥ 10 := by omega 
      exact Nat.pow_le_pow_of_le_right (by norm_num) this 
    have h7 : 3^x + 3^y + 3^z ≥ 3^z := by 
      linarith [show 0 ≤ (3^x : ℕ) by positivity, show 0 ≤ (3^y : ℕ) by positivity]
    have h8 : 3^z ≤ 21897 := by 
      linarith [h₂, h7]
    norm_num at h6 h8 
    all_goals linarith

  have h3' : x ≤ 9 := h3 
  have h4' : y ≤ 9 := h4 
  have h5' : z ≤ 9 := h5 
  interval_cases x <;> interval_cases y <;> interval_cases z 
    <;> norm_num [Prod.ext_iff] at h₂ ⊢ 
    <;> tauto