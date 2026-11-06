import Mathlib

theorem algebra_149909 {a b c : ℝ} (habc : a ≠ b ∧ b ≠ c ∧ a ≠ c) :
    ((a + b) * (a^3 + b^3)) / ((b - c) * (c - a)) -
    ((b + c) * (b^3 + c^3)) / ((a - c) * (a - b)) +
    ((a + c) * (a^3 + c^3)) / ((b - c) * (a - b)) = a * b + b * c + c * a := by

  have hab1 : a ≠ b := habc.1
  have hab2 : b ≠ c := habc.2.1
  have hab3 : a ≠ c := habc.2.2

  have h1 : a - b ≠ 0 := sub_ne_zero_of_ne hab1
  have h2 : b - c ≠ 0 := sub_ne_zero_of_ne hab2
  have h3 : a - c ≠ 0 := sub_ne_zero_of_ne hab3
  have h4 : c - a ≠ 0 := by
    intro h
    apply hab3
    linarith
  -- These non-zero differences are important to ensure division is defined.
  field_simp [h1, h2, h3, h4, mul_comm]
  ring