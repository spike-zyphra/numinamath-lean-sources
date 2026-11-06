import Mathlib

theorem algebra_11298 {S : Finset ℕ} (hS : S = {2^0, 2^1, 2^2, 2^3, 2^4, 2^5, 2^6, 2^7, 2^8, 2^9, 2^10}) :
    ∑ x ∈ S, ∑ y ∈ S, (if x > y then x - y else 0) = 16398 := by 
  rw [hS]
  native_decide