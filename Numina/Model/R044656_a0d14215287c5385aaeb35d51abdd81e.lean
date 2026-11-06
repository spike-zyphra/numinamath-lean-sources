import Mathlib

theorem algebra_235686 (n : ℕ) (h₀ : n > 0) (h₁ : (n * 90 + 97) / (n + 1) = 97)
    (h₂ : (n * 87 + 73) / (n + 1) = 73) :
    n = 8 := by
  have h3 : n + 1 > 0 := by
    omega
  have h16 : (n * 90 + 97) = 97 * (n + 1) + ((n * 90 + 97) % (n + 1)) := by
    have h5 : (n * 90 + 97) % (n + 1) + (n + 1) * ((n * 90 + 97) / (n + 1)) = (n * 90 + 97) := by
      rw [Nat.mod_add_div]
    have h6 : (n * 90 + 97) / (n + 1) = 97 := h₁
    calc 
      (n * 90 + 97) = (n * 90 + 97) % (n + 1) + (n + 1) * ((n * 90 + 97) / (n + 1)) := by 
        linarith [h5]
      _ = (n * 90 + 97) % (n + 1) + (n + 1) * 97 := by 
          rw [h6]
      _ = 97 * (n + 1) + (n * 90 + 97) % (n + 1) := by 
        ring
  have h10 : (n * 87 + 73) = 73 * (n + 1) + ((n * 87 + 73) % (n + 1)) := by
    have h5 : (n * 87 + 73) % (n + 1) + (n + 1) * ((n * 87 + 73) / (n + 1)) = (n * 87 + 73) := by
      rw [Nat.mod_add_div]
    have h6 : (n * 87 + 73) / (n + 1) = 73 := h₂
    calc 
      (n * 87 + 73) = (n * 87 + 73) % (n + 1) + (n + 1) * ((n * 87 + 73) / (n + 1)) := by 
        linarith [h5]
      _ = (n * 87 + 73) % (n + 1) + (n + 1) * 73 := by 
          rw [h6]
      _ = 73 * (n + 1) + (n * 87 + 73) % (n + 1) := by 
        ring
  omega