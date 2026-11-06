import Mathlib

theorem number_theory_188685 :
    ∃ x y : ℝ, Irrational x ∧ Irrational y ∧ ¬Irrational (x + y) := by
  use Real.sqrt 2, -Real.sqrt 2
  constructor
  · -- Show that sqrt 2 is irrational
    native_decide
  constructor
  · -- Show that -sqrt 2 is irrational
    apply Irrational.neg
    native_decide
  · -- Show that sqrt 2 + (-sqrt 2) is not irrational
    simp [show Real.sqrt 2 + (-Real.sqrt 2) = (0 : ℝ) by ring]
    all_goals norm_num
    <;> try { native_decide }