import Mathlib

open Finset

theorem number_theory_324707 {a b : ℕ} (ha : a > 1) (hb : b > 1)
    (h : ∃ x y z, x > 0 ∧ y > 0 ∧ z > 0 ∧ x + y + z = a ^ b ∧ max (max x y) z = 1) :
    a = 2 ∧ b = 3 ∨ ∃ k, a = 3 ^ k := by
  rcases h with ⟨x, y, z, hx, hy, hz, h_eq, h_max⟩
  have h1 : x ≤ 1 := by 
    have h2 : max (max x y) z = 1 := h_max
    have h3 : x ≤ max (max x y) z := by 
      simp [le_max_iff]
    rw [h2] at h3 
    omega 
  have h2 : y ≤ 1 := by 
    have h3 : max (max x y) z = 1 := h_max
    have h4 : y ≤ max (max x y) z := by 
      simp [le_max_iff]
    rw [h3] at h4 
    omega 
  have h3 : z ≤ 1 := by 
    have h4 : max (max x y) z = 1 := h_max
    have h5 : z ≤ max (max x y) z := by 
      simp [le_max_iff]
    rw [h4] at h5 
    omega 
  have h4 : x = 1 := by 
    omega 
  have h5 : y = 1 := by 
    omega 
  have h6 : z = 1 := by 
    omega 
  -- x + y + z = a^b => 3 = a^b
  have h_eq1 : a ^ b = 3 := by
    nlinarith [h_eq, h4, h5, h6] 
  have h_eq2 : a ^ b = 3 := h_eq1
  have h_eq3 : b ≥ 2 := by 
    omega 
  have h_eq4 : a ≥ 2 := by 
    omega 
  -- Now need to show that a^b >= 4, which contradicts a^b = 3
  have h_eq5 : a ^ b ≥ a ^ 2 := by
    have h6 : b ≥ 2 := by 
      omega 
    have h7 : a ^ b ≥ a ^ 2 := by
      apply Nat.pow_le_pow_of_le_right 
      all_goals 
        omega 
    linarith 
  have h_eq6 : a ^ 2 ≥ 4 := by 
    nlinarith [h_eq4] 
  -- Thus a^b >= 4
  have h_eq7 : a ^ b ≥ 4 := by 
    nlinarith [h_eq5, h_eq6] 
  -- But a^b = 3
  nlinarith [h_eq1, h_eq7]