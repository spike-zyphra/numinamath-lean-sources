import Mathlib

theorem algebra_139701 (a : ℝ) (ha : a ≠ 0) (P : ℝ → ℝ → ℝ)
    (hP : P = fun x y => y - a^3 * x^2 / 3 - a^2 * x / 2 + 2 * a) :
    ∃ x y, P x y = 0 ∧ x * y = 105 / 64 := by 
  use -3 / (4 * a)
  use -35 * a / 16 
  constructor 
  · -- Show that $P(-3/(4*a), -35*a/16) = 0$
    simp [hP]
    field_simp [ha]
    ring 
  · -- Show that $(-3/(4*a)) * (-35*a/16) = 105/64$
    field_simp [ha]
    ring