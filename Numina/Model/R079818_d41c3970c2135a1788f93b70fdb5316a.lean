import Mathlib

theorem number_theory_150605 (n : ℕ) (a : Fin n → ℤ) (h : 5 ∣ ∑ i : Fin n, a i) :
    5 ∣ ∑ i : Fin n, (a i)^5 := by
  have h1 : ∀ x : ℤ, (x ^ 5) % 5 = x % 5 := by
    intro x 
    have h1 : (x ^ 5 : ℤ) % 5 = x % 5 := by 
      have h2 : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by 
          omega 
      rcases h2 with (h2 | h2 | h2 | h2 | h2)
      · 
        simp [h2, pow_succ, Int.mul_emod, Int.add_emod, Int.mul_emod, Int.sub_emod] 
      · 
        simp [h2, pow_succ, Int.mul_emod, Int.add_emod, Int.mul_emod, Int.sub_emod] 
      · 
        simp [h2, pow_succ, Int.mul_emod, Int.add_emod, Int.mul_emod, Int.sub_emod] 
      · 
        simp [h2, pow_succ, Int.mul_emod, Int.add_emod, Int.mul_emod, Int.sub_emod] 
      · 
        simp [h2, pow_succ, Int.mul_emod, Int.add_emod, Int.mul_emod, Int.sub_emod] 
    exact h1 
  have h2 : (∑ i : Fin n, (a i) ^ 5) % 5 = (∑ i : Fin n, (a i) ) % 5 := by
    have h3 : ∀ (i : Fin n), (a i) ^ 5 % 5 = (a i) % 5 := by 
      intro i 
      apply h1 
    simp [Finset.sum_int_mod, h3] 
  omega