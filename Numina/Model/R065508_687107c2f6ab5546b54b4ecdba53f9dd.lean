import Mathlib

theorem algebra_205086 (x : ℝ) :
    (540 + x = 700 ↔ x = 160) ∧
    (5400 + x = 7000 ↔ x = 1600) ∧
    (54000 + x = 70000 ↔ x = 16000) ∧
    (540000 + x = 700000 ↔ x = 160000) := by
  constructor
  · -- Forward and back for the first
    constructor
    · -- Forward: if 540 + x = 700, then x = 160
      intro h
      linarith
    · -- Back: if x = 160, then 540 + x = 700
      intro h
      linarith
  constructor
  · -- Forward and back for the second
    constructor
    · -- Forward: if 5400 + x = 7000, then x = 1600
      intro h
      linarith
    · -- Back: if x = 1600, then 5400 + x = 7000
      intro h
      linarith
  constructor
  · -- Forward and back for the third
    constructor
    · -- Forward: if 54000 + x = 70000, then x = 16000
      intro h
      linarith
    · -- Back: if x = 16000, then 54000 + x = 70000
      intro h
      linarith
  · -- Forward and back for the fourth
    constructor
    · -- Forward: if 540000 + x = 700000, then x = 160000
      intro h
      linarith
    · -- Back: if x = 160000, then 540000 + x = 700000
      intro h
      linarith