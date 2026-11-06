import Mathlib

theorem algebra_132428 {x y : ℕ} (h : x ≠ 0) (h' : y ≠ 0)
    (h1 : (x + 2) * (y - 2) = x * y) :
    IsSquare (x * y + 1) := by 
  by_cases hy : y > 2
  · -- y > 2
    have eq1 : y - 2 + 2 = y := by omega
    have eq3 : y = x + 2 := by
      have h_eq : (x + 2) * (y - 2) = x * y := h1
      cases y with
      | zero => contradiction
      | succ y =>
        cases y with
        | zero => contradiction
        | succ y =>
          cases y with
          | zero => omega
          | succ y =>
            simp [Nat.mul_add, Nat.add_mul, Nat.mul_sub_left_distrib, Nat.sub_sub] at h_eq ⊢
            all_goals
              ring_nf at h_eq ⊢
              all_goals
                omega
    have eq4 : x * y + 1 = (x + 1) ^ 2 := by
      rw [show y = x + 2 by exact eq3]
      ring
    rw [eq4]
    exact ⟨x + 1, by ring⟩
  · -- y ≤ 2 
    have h2 : y ≤ 2 := by omega
    have h3 : y = 1 ∨ y = 2 := by
      interval_cases y <;> omega 
    rcases h3 with (h3 | h3)
    · -- y = 1 
      have h6 : y = 1 := h3 
      rw [h6] at h1
      simp [Nat.mul_zero] at h1 
      all_goals
        exfalso
        have hx : x > 0 := by
          by_contra h8
          push_neg at h8 
          have : x = 0 := by 
            omega 
          contradiction
        exfalso 
        nlinarith [h1, show x > 0 by linarith [h]]
    · -- y = 2 
      have h7 : y = 2 := h3 
      rw [h7] at h1
      simp [Nat.mul_zero] at h1 
      all_goals 
        exfalso 
        have hx : x > 0 := by 
          by_contra h8
          push_neg at h8 
          have : x = 0 := by
            omega 
          contradiction 
        exfalso 
        nlinarith [h1, show x > 0 by linarith [h]]