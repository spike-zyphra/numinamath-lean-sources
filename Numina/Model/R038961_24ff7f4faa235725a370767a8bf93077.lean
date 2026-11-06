import Mathlib

theorem algebra_94572 (x y z : ℕ) (h₀ : x > 0) (h₁ : y > 0) (h₂ : z > 0)
    (h₃ : z ^ x = y ^ (2 * x)) (h₄ : 2 ^ z = 2 * 4 ^ x) (h₅ : x + y + z = 16) :
    x = 4 ∧ y = 3 ∧ z = 9 := by 
  have eq1 : z = 1 + 2 * x := by
    have eq2 : (2 : ℕ) ^ z = 2 * (4 : ℕ) ^ x := by
      linarith [h₄]
    have eq3 : (2 * (4 : ℕ) ^ x) = (2 : ℕ) ^ (1 + 2 * x) := by
      rw [show (4 : ℕ) ^ x = (2 : ℕ) ^ (2 * x) by
        rw [show (4 : ℕ) = (2 : ℕ) ^ (2 : ℕ) by norm_num]
        rw [← pow_mul]
      ]
      ring_nf
    rw [eq3] at eq2
    have h1 : z = 1 + 2 * x := by
      exact Nat.pow_right_injective (by norm_num) eq2
    exact h1
  have eq2 : y = 15 - 3 * x := by
    rw [show z = 1 + 2 * x by linarith [eq1]] at h₅
    omega
  have h6 : x ≤ 4 := by
    have h7 : y > 0 := h₁
    rw [eq2] at h7
    omega
  interval_cases x <;> norm_num [eq1, eq2] at h₃ h₅ h₁ h₂ ⊢ 
  <;> omega 
  <;> tauto