import Mathlib

theorem algebra_21862 :
    (Finset.filter (λ n => 3 ∣ n ∧ 4 ∣ n ∧ 5 ∣ n) (Finset.Icc 1 500)).card = 8 := by
  rfl