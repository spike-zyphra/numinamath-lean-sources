import Mathlib

theorem algebra_270300 {x y z : ℝ} (h₀ : x + y + z = 6) (h₁ : x * y + y * z + z * x = 11) (h₂ : x * y * z = 6) :
    (x = 1 ∧ y = 2 ∧ z = 3) ∨ (x = 1 ∧ y = 3 ∧ z = 2) ∨ (x = 2 ∧ y = 1 ∧ z = 3) ∨
    (x = 2 ∧ y = 3 ∧ z = 1) ∨ (x = 3 ∧ y = 1 ∧ z = 2) ∨ (x = 3 ∧ y = 2 ∧ z = 1) := by
  have h3 : (x - 1) * (x - 2) * (x - 3) = 0 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 2), sq_nonneg (x - 3), 
            sq_nonneg (y - 1), sq_nonneg (y - 2), sq_nonneg (y - 3), 
            sq_nonneg (z - 1), sq_nonneg (z - 2), sq_nonneg (z - 3)]
  cases' (mul_eq_zero.mp h3) with h4 h5
  cases' (mul_eq_zero.mp h4) with h6 h7
  · -- Case x = 1
    have hx1 : x = 1 := by linarith 
    have h31 : (y - 2) * (y - 3) = 0 := by 
      have h41 : y + z = 5 := by linarith [h₀, hx1]
      have h42 : y * z = 6 := by 
        have : x * y * z = 6 := h₂
        rw [hx1] at this 
        nlinarith
      nlinarith [sq_nonneg (y - 2), sq_nonneg (y - 3), sq_nonneg (z - 2), sq_nonneg (z - 3)]
    cases' (mul_eq_zero.mp h31) with h8 h9 
    · -- Case x = 1, y = 2, then z = 3 
      have hy1 : y = 2 := by linarith 
      have hz1 : z = 3 := by linarith [h₀, hx1, hy1]
      left 
      tauto
    · -- Case x = 1, y = 3, then z = 2 
      have hy1 : y = 3 := by linarith 
      have hz1 : z = 2 := by linarith [h₀, hx1, hy1]
      right
      left
      tauto
  · -- Case x = 2
    have hx1 : x = 2 := by linarith 
    have h31 : (y - 1) * (y - 3) = 0 := by 
      have h41 : y + z = 4 := by linarith [h₀, hx1]
      have h42 : y * z = 3 := by 
        have : x * y * z = 6 := h₂
        rw [hx1] at this
        nlinarith
      nlinarith [sq_nonneg (y - 1), sq_nonneg (y - 3), sq_nonneg (z - 1), sq_nonneg (z - 3)]
    cases' (mul_eq_zero.mp h31) with h8 h9
    · -- Case x = 2, y = 1, then z = 3 
      have hy1 : y = 1 := by linarith 
      have hz1 : z = 3 := by linarith [h₀, hx1, hy1]
      right 
      right
      left 
      tauto
    · -- Case x = 2, y = 3, then z = 1
      have hy1 : y = 3 := by linarith 
      have hz1 : z = 1 := by linarith [h₀, hx1, hy1]
      right 
      right 
      right 
      left 
      tauto
  · -- Case x = 3
    have hx1 : x = 3 := by linarith 
    have h31 : (y - 1) * (y - 2) = 0 := by 
      have h41 : y + z = 3 := by linarith [h₀, hx1]
      have h42 : y * z = 2 := by
        have : x * y * z = 6 := h₂
        rw [hx1] at this
        nlinarith 
      nlinarith [sq_nonneg (y - 1), sq_nonneg (y - 2), sq_nonneg (z - 1), sq_nonneg (z - 2)]
    cases' (mul_eq_zero.mp h31) with h8 h9 
    · -- Case x = 3, y = 1, then z = 2 
      have hy1 : y = 1 := by linarith 
      have hz1 : z = 2 := by linarith [h₀, hx1, hy1]
      right 
      right
      right 
      right 
      left 
      tauto 
    · -- Case x = 3, y = 2, then z = 1 
      have hy1 : y = 2 := by linarith 
      have hz1 : z = 1 := by linarith [h₀, hx1, hy1]
      right
      right
      right
      right 
      right 
      tauto