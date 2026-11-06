import Mathlib

theorem number_theory_304193 : {x : ℤ | ∃ n, x = n ∧ n ∈ Finset.Icc 1 6}.encard = 6 := by
  have h1 : {x : ℤ | ∃ n, x = n ∧ n ∈ Finset.Icc 1 6} = {1, 2, 3, 4, 5, 6} := by
    ext x
    simp [Finset.mem_Icc]
    <;> omega
  rw [h1]
  rw [Set.encard]
  simp
  <;> try { tauto }
  all_goals try { native_decide }