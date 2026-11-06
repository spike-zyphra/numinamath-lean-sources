import Mathlib

theorem number_theory_99408 {n : ℕ} (hn : ∏ i ∈ Finset.range 201, (401^(2*i + 1)) = 401^(n^2)) :
    n = 201 := by 
  have h1 : ∏ i in Finset.range 201, (401 ^ (2 * i + 1)) = 401 ^ (∑ i in Finset.range 201, (2 * i + 1)) := by 
    rw [Finset.prod_pow_eq_pow_sum]
  rw [h1] at hn
  have h2 : ∑ i in Finset.range 201, (2 * i + 1) = 201 ^ 2 := by 
    native_decide
  rw [h2] at hn
  have h3 : 201 ^ 2 = n ^ 2 := by 
    have h4 : 401 ^ (201 ^ 2) = 401 ^ (n ^ 2) := by 
      exact_mod_cast hn
    have h5 : 201 ^ 2 = n ^ 2 := by 
      exact Nat.pow_right_injective (by norm_num) h4
    exact_mod_cast h5
  have h6 : n = 201 := by
    nlinarith 
  exact_mod_cast h6