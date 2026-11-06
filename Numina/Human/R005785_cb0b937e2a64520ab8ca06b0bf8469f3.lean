import Mathlib

def decimal_digit_mod (num denom : ℕ) (pos : ℕ) : ℕ :=
  let rec compute_digit (remainder : ℕ) (position : ℕ) : ℕ :=
    if position = 0 then
      (remainder * 10) / denom
    else
      let new_remainder := (remainder * 10) % denom
      compute_digit new_remainder (position - 1)
  compute_digit (num % denom) pos

theorem number_theory_609915 :
  decimal_digit_mod 1 998 9997 = 0 ∧
  decimal_digit_mod 1 998 9998 = 4 ∧
  decimal_digit_mod 1 998 9999 = 2 := by
  native_decide
