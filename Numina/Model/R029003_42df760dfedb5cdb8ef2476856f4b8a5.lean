import Mathlib


theorem number_theory_179853 : ∃ n>10, ∃a : Fin n → ℕ, ∑ i, a i = 20 ∧
    (∀ i, a i ≠ 3 ∧ a i ≠ 0) ∧ ∀ j k, ∑ i in Finset.Icc j k, a i ≠ 3 := by
  use 11
  constructor
  · norm_num
  use (fun i =>
    if i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 4 ∨ i = 6 ∨ i = 7 ∨ i = 9 ∨ i = 10 then 1
    else if i = 2 ∨ i = 5 ∨ i = 8 then 4
    else 0
  )
  constructor
  · -- Show the total sum is 20
    native_decide
  constructor
  · -- Show that all elements are neither 0 nor 3
    intro i
    fin_cases i <;> simp <;> try { tauto }
  · -- Show that no consecutive sum equals 3
    intro j k
    fin_cases j <;> fin_cases k <;> simp [Finset.sum_Icc_succ_top, Finset.sum_singleton] <;> try { native_decide }