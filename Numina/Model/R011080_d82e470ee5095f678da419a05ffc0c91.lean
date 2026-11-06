import Mathlib

/- A positive integer is "mild" if its base-3 representation never contains the digit 2. -/
@[reducible]
def mild (n : ℕ) :=
    0 < n ∧ 2 ∉ Nat.digits 3 n

theorem number_theory_611045 :
    { n ∈ Finset.Icc 1 1000 | mild n ∧ mild (n ^ 2) }.card = 7 := by
  have h1 : {n ∈ Finset.Icc 1 1000 | mild n ∧ mild (n ^ 2)} = 
      Finset.filter (fun n => (0 < n ∧ 2 ∉ Nat.digits 3 n) ∧ (0 < n ^ 2 ∧ 2 ∉ Nat.digits 3 (n ^ 2))) (Finset.Icc 1 1000) := by 
    ext n
    simp [mild]
  rw [h1]
  rw [Finset.filter]
  simp [Finset.Icc]
  <;> native_decide