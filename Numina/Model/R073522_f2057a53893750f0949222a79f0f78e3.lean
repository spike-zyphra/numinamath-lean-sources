import Mathlib

theorem number_theory_294407 : {x : ℕ | Odd x ∧ x ∈ Finset.Icc 1 2019}.encard = 1010 := by 
  have h1 : {x : ℕ | Odd x ∧ x ∈ Finset.Icc 1 2019} = Finset.filter (fun x : ℕ => Odd x) (Finset.Icc 1 2019) := by
    ext n
    simp
    <;> tauto 
  rw [h1]
  rw [Finset.filter]
  simp [Finset.Icc]
  <;> try native_decide