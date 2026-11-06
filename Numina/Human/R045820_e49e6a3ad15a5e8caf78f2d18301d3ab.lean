import Mathlib

theorem algebra_255042 {f : ℕ → ℕ} (hf : f = fun x ↦ 3 * x + 2) : ∃ m, 0 < m ∧ 1997 ∣ f^[99] m := by
  rw [hf]
  use 3 ^ 1897 - 1

  constructor
  · -- Show m > 0
    have h1: 0 < 3 ^ 1897 - 1 := by
      have h1: 1 < 3 ^ 1897 := by 
        norm_num
      exact Nat.sub_pos_of_lt h1
    exact h1
  · -- Show 1997 ∣ f^[99] (3 ^ 1897 - 1)
    native_decide