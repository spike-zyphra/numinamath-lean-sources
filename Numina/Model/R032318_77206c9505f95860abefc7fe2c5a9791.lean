import Mathlib

theorem number_theory_307614 :
    Set.ncard {n : ℕ | 0 < n ∧ n ≤ 2011 ∧ IsSquare (1 + 17 * n)} = 20 := by
  have h1 : {n : ℕ | 0 < n ∧ n ≤ 2011 ∧ IsSquare (1 + 17 * n)} = Finset.filter (fun n => 0 < n ∧ n ≤ 2011 ∧ IsSquare (1 + 17 * n)) (Finset.Icc 0 2011) := by 
    ext n
    simp
    <;> omega 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide