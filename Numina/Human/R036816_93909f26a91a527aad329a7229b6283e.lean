import Mathlib

open Real Set
open scoped BigOperators

/- Find the smallest possible value of $$\frac{(y-x)^2}{(y-z)(z-x)} + \frac{(z-y)^2}{(z-x)(x-y)} + \frac{(x-z)^2}{(x-y)(y-z)},$$ where $x,y,$ and $z$ are distinct real numbers. -/
theorem algebra_19878 :
  IsLeast {t : ℝ | ∃ x y z : ℝ, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ t = ((y - x)^2 / ((y - z) * (z - x)) +
    (z - y)^2 / ((z - x) * (x - y)) + (x - z)^2 / ((x - y) * (y - z)))} 3 := by
  constructor
  -- $3$ is a possible value
  use 0
  use 1
  use 2
  norm_num
  -- $3$ is the least such value
  intro n nin
  rcases nin with ⟨x, y, z, xney, ynez, znex, neq⟩
  have neq2 : n = 3 := by
    rw [neq]
    have xyne : x - y ≠ 0 := by
      exact sub_ne_zero_of_ne xney
    have yzne : y - z ≠ 0 := by
      exact sub_ne_zero_of_ne ynez
    have zxne : z - x ≠ 0 := by
      exact sub_ne_zero_of_ne znex
    field_simp
    ring_nf
  rw [neq2]
