import Mathlib

theorem algebra_238028 {x y : ℕ} (hy : y ≠ 0) (h : x / y = 11) (h' : (x + 1650) / y = 11 + 7 * (x / y)) :
    x = 25275 := by
  have h1 : (x + 1650) / y = 88 := by
    omega
  have h3 : x = 11 * y + (x % y) := by 
    have h4 : x / y = 11 := h
    have h5 : x = y * (x / y) + (x % y) := by
      rw [Nat.div_add_mod x y]
    rw [h4] at h5
    all_goals linarith
  have h6 : x + 1650 = 88 * y + ((x + 1650) % y) := by
    have h1' : (x + 1650) / y = 88 := h1
    have h7 : (x + 1650) = y * ((x + 1650) / y) + ((x + 1650) % y) := by
      rw [Nat.div_add_mod (x + 1650) y]
    rw [h1'] at h7
    all_goals linarith
  have h8 : (x + 1650) % y < y := by
    apply Nat.mod_lt
    omega
  have h9 : x % y < y := by
    apply Nat.mod_lt
    omega
  have h10 : x % y + 1650 = 77 * y + ((x + 1650) % y) := by
    omega
  omega