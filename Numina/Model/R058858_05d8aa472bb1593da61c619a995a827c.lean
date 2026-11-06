import Mathlib

theorem number_theory_212013 : {x : ℕ | Odd x ∧ 300 ≤ x ∧ x < 700}.encard = 200 := by
  have h1 : {x : ℕ | Odd x ∧ 300 ≤ x ∧ x < 700} = Finset.filter (fun x => Odd x) (Finset.Icc 300 699) := by
    ext n
    simp [Nat.odd_iff, Finset.mem_Icc]
    <;> omega
  rw [h1]
  rw [Finset.filter]
  simp [Finset.Icc]
  <;> try native_decide