import Mathlib

theorem algebra_6415 (x : ℕ) : (19^x + 2020) = 322687699799 → x = 9 := by 
  intro h_eq
  have h1 : 19 ^ x = 322687697779 := by 
    omega
  have h2 : x = 9 := by 
    have h3 : 19 ^ 9 = 322687697779 := by 
      norm_num
    have h4 : 19 ^ x = 19 ^ 9 := by 
      rw [h1] 
      rw [h3]
    have h5 : x = 9 := by 
      exact Nat.pow_right_injective (by norm_num) h4
    exact h5
  exact h2