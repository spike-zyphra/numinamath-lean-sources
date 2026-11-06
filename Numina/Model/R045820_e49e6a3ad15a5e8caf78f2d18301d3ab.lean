import Mathlib

theorem algebra_255042 {f : ℕ → ℕ} (hf : f = fun x ↦ 3 * x + 2) : ∃ m, 0 < m ∧ 1997 ∣ f^[99] m := by 
  use 3 ^ 1897 - 1
  constructor
  · -- Show that 0 < m
    norm_num
  · -- Show that 1997 divides f^[99] m
    rw [hf]
    native_decide