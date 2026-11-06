import Mathlib

theorem algebra_121561 (x y z : ℝ) (h₀ : x + y + z - 2 = 0) (h₁ : x - y - 2 * z + 2 = 0) :
    x / (-1) = (y - 2) / 3 ∧ (y - 2) / 3 = z / (-2) := by

  have h2 : z = 2 * x := by
    nlinarith

  have h3 : y = -3 * x + 2 := by
    nlinarith [h₀, h₁, h2]

  constructor
  · -- Prove the first equality: x / (-1) = (y - 2) / 3
    have eq1 : x / (-1) = (y - 2) / 3 := by
      rw [show y = -3 * x + 2 by linarith [h3]]
      field_simp
      <;> linarith
    exact eq1
  · -- Prove the second equality: (y - 2) / 3 = z / (-2)
    have eq2 : (y - 2) / 3 = z / (-2) := by
      rw [show y = -3 * x + 2 by linarith [h3], show z = 2 * x by linarith [h2]]
      field_simp
      <;> linarith
    exact eq2