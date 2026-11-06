import Mathlib

def isWeird (n : ℕ) := ¬(n ∣ Nat.factorial (n - 2))

theorem number_theory_172355 : {n | 2 ≤ n ∧ n ≤ 100 ∧ isWeird n}.encard = 26 := by
  have h1 : {n | 2 ≤ n ∧ n ≤ 100 ∧ isWeird n} = 
          (Finset.Icc 2 100).filter (fun n => ¬(n ∣ Nat.factorial (n - 2))) := by 
    ext n
    simp [isWeird]
    <;> tauto 
  rw [h1]
  rw [Finset.filter]
  simp [isWeird]
  <;> try native_decide
  <;> try aesop
  <;> try native_decide