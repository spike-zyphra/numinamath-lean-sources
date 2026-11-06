import Mathlib

theorem algebra_214023 {A : ℕ} (hA : 20000 + 1000 * A + 99561 = (3 * (523 + A)) ^ 2) :
    A = 4 := by
  have h1 : A ≤ 9 := by
    nlinarith [hA]
  interval_cases A <;> omega