import Mathlib

open Nat

theorem my_favorite_theorem {b : ℕ}(hb : b > 2)  (N : ℕ) (hN : digits b N = [2, 2, 2, 1]) :
    N = b^3 + 2 * b^2 + 2 * b + 2 := by
  -- Step 1: Reconstruct N from its digits using ofDigits
  have h_reconstruct : ofDigits b [2, 2, 2, 1] = N := by
    rw [← hN, ofDigits_digits b N ]
  
  -- Step 2: Compute ofDigits explicitly
  simp [ofDigits] at h_reconstruct
  
  -- Step 3: Simplify the expression
  rw [← h_reconstruct]
  repeat rw[mul_add]
  rw [← mul_assoc]
  repeat rw [← add_assoc]
  simp [← pow_three]
  rw [← pow_two]
  rw [mul_comm]
  rw [add_comm]
  nth_rw 2[add_comm]
  rw [mul_comm]
  nth_rw 3[add_comm]
  rw[← add_assoc,← add_assoc]