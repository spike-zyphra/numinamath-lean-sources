import Mathlib

theorem number_theory_53825 (m n : ℕ) (hm : 111 ∣ m) (hn : 31 ∣ n) (hsum : m + n = 2017) :
    n - m = 463 := by 
  rcases hm with ⟨k, hk⟩
  rcases hn with ⟨j, hj⟩
  omega