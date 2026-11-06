import Mathlib

theorem number_theory_109415 :
    Set.ncard {n : ℕ | Odd n ∧ Odd (10 * (n % 10) + (n / 10)) ∧ n ∈ Finset.Icc 10 99} = 25 := by 
  have h1 : {n : ℕ | Odd n ∧ Odd (10 * (n % 10) + (n / 10)) ∧ n ∈ Finset.Icc 10 99} = Finset.filter (fun n => Odd n ∧ Odd (10 * (n % 10) + (n / 10))) (Finset.Icc 10 99) := by
    ext n
    simp [Finset.mem_Icc]
    <;> tauto 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide