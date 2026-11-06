import Mathlib

theorem number_theory_197496 {A : ℕ} (hA : A > 0) (hA1 : A % 10000 = 16 * 3333 + 2227) :
    A = 55555 := by
  omega