import Mathlib

theorem algebra_227400 {x y: ℕ} (h1: x / y = 74) (h2: x % y = 22)
(h: x = 74 * 60 + 30214): x = 34654 ∧ y = 468 := by
  have hx : x = 34654 := by 
    omega
  have hy : y = 468 := by 
    rw [hx] at h1 h2 
    have h3 : 34654 = y * 74 + 22 := by
      have h4 : 34654 % y = 22 := h2 
      have h5 : 34654 / y = 74 := h1 
      have h6 : 34654 = y * (34654 / y) + (34654 % y) := by 
        rw [Nat.div_add_mod 34654 y] 
      rw [h5, h4] at h6 
      linarith 
    have h4 : y ≤ 34654 := by 
      by_contra h5 
      push_neg at h5 
      have h7 : 34654 % y = 34654 := by 
        rw [Nat.mod_eq_of_lt] 
        all_goals linarith 
      omega 
    have h2' : y > 22 := by 
      by_contra h 
      push_neg at h 
      interval_cases y <;> omega 
    have h8 : y = 468 := by 
      omega 
    exact h8 
  exact ⟨hx, hy⟩