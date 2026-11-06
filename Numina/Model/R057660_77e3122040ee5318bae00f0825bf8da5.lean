import Mathlib

theorem algebra_14501 {x : ℕ} (hx : x^5 = 2^10 * 2^15) : x = 32 := by
  have h1 : x^5 = 2^25 := by
    calc
      x^5 = 2^10 * 2^15 := hx
      _ = 2^(10 + 15) := by rw [pow_add]
      _ = 2^25 := by norm_num
  have h2 : x^5 = 32^5 := by
    calc
      x^5 = 2^25 := h1
      _ = (2^5)^5 := by ring
      _ = 32^5 := by norm_num
  have h3 : x = 32 := by
    rw [Nat.pow_left_injective (by norm_num) h2]
  exact h3