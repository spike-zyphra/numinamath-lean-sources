import Mathlib

def sol := 128

theorem number_theory_4766 : {x | Odd x ∧ x ∣ 9699690}.encard = sol := by
  have h1 : {x | Odd x ∧ x ∣ 9699690} = Finset.filter (fun x => Odd x) (Nat.divisors 9699690) := by
    ext n
    simp [Nat.odd_iff]
    <;> tauto
  rw [h1]
  rw [Finset.filter]
  simp [Nat.odd_iff]
  <;> try native_decide
  <;> try simp [sol]
  <;> try native_decide