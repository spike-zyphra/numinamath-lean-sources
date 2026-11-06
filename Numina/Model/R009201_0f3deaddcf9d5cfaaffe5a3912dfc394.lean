import Mathlib

theorem algebra_13890 : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ 9 ∣ n}.ncard = 10 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ 9 ∣ n} = Finset.filter (fun x => 9 ∣ x) (Finset.Icc 10 99) := by
    ext n
    simp 
  rw [h1]
  rw [Finset.filter]
  simp [Finset.Icc]
  <;> try { aesop }
  <;> try { native_decide }