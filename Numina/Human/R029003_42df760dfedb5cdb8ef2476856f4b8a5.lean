import Mathlib

/- Shapovalov A.V.

Several natural numbers are written in a row with a sum of 20. No number and no sum of several consecutive numbers equals 3. Could there be more than 10 numbers written? -/
theorem number_theory_179853 : ∃ n>10, ∃a : Fin n → ℕ, ∑ i, a i = 20 ∧
    (∀ i, a i ≠ 3 ∧ a i ≠ 0) ∧ ∀ j k, ∑ i in Finset.Icc j k, a i ≠ 3 := by
  -- the 11 number sequence 1,1,4,1,1,4,1,1,4,1,1 fulfills all the requirements
  use 11
  constructor
  . simp
  let a : Fin 11 → ℕ  := fun i => match i with
    | 0|1|3|4|6|7|9|10 => 1
    | 2|5|8 => 4
  use a
  constructorm* _ ∧ _
  case left => rfl
  case right.left =>
    intro i
    simp only [a]
    fin_cases i <;> trivial
  case right.right =>
    intro j k
    fin_cases j <;> fin_cases k <;> trivial