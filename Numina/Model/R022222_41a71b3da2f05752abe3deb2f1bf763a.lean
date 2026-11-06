import Mathlib

theorem algebra_12797 {M N : Set ℕ} (hM : M = {1, 2}) (hN : N = {x | ∃ a ∈ M, x = 2 * a - 1}) :
    M ∩ N = {1} := by 
  rw [hN]
  rw [hM]
  ext x
  simp
  omega