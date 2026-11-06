import Mathlib

theorem algebra_175890 {x y z : ℕ} (hy : y ≠ 0) (h : x * 5 = y * 4 + z * 1) :
    x / (x + y + z) = 2 / 5 := by
  have h1 : y > 0 := by
    by_contra h2
    push_neg at h2
    have h3 : y = 0 := by
      omega
    contradiction
  have h2 : x < x + y + z := by 
    omega
  have h3 : x / (x + y + z) = 0 := by 
    have h4 : x < x + y + z := by 
      omega
    have : x / (x + y + z) = 0 := by
      rw [Nat.div_eq_zero_iff]
      omega
    exact this
  calc 
    x / (x + y + z) = 0 := h3
    _ = 2 / 5 := by norm_num