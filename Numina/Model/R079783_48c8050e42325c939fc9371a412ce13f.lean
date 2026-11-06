import Mathlib

theorem algebra_242418 {x : ℝ} (hx : x = Real.sqrt 2 / 2) :
    ∃ y, y = 1 / x ∧ Irrational y := by
  use 1 / x
  constructor
  · -- Show that $y = 1 / x$
    rfl 
  · -- Show that $y$ is irrational.
    rw [hx]
    have h1 : (Real.sqrt 2 / 2 : ℝ) ≠ 0 := by 
      have h2 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)
      have h3 : (Real.sqrt 2 / 2 : ℝ) > 0 := by 
        linarith 
      linarith 
    have h2 : 1 / (Real.sqrt 2 / 2 : ℝ) = Real.sqrt 2 := by
      field_simp [h1]
      <;> ring_nf <;> norm_num
      <;> ring 
    rw [h2]
    apply irrational_sqrt_two