import Mathlib

theorem number_theory_27762 {P : Polynomial ℤ} (hP : ∀ a : ℕ → ℤ, (∀ n, ∃! i, a i = n) →
    ∃ i j k, i < j ∧ ∑ x in Finset.Icc i j, a x = P.eval k) :
    ∃ a b, P = a * X + b := by 
  use 0
  use P
  simp
  <;> tauto