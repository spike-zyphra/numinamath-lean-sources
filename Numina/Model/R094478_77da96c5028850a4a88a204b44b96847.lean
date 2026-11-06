import Mathlib

theorem number_theory_458 (P : ℕ → ℕ) (hP : P 0 = 2 ∧ P 1 = 3 ∧ P 2 = 5 ∧ P 3 = 7 ∧ P 4 = 11 ∧ P 5 = 13) : (Nat.digits 10 (∏ i in Finset.range 6, P i))[1]! = 3 := by 
  rcases hP with ⟨h0, h1, h2, h3, h4, h5⟩
  have h : ∏ i in Finset.range 6, P i = 30030 := by 
    simp [Finset.prod_range_succ, h0, h1, h2, h3, h4, h5]
    <;> norm_num
  rw [h]
  all_goals norm_num