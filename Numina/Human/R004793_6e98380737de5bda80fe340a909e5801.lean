import Mathlib

theorem algebra_325860 :
    (∀x, ∀a ≠ 0, (√(x^2) = a) → (x = -a ∨ x = a)) ∧
    ¬(∀x, ∀a ≠ 0, (x = -a ∨ x = a) → (√(x^2) = a)) := by
  simp
  constructor
  · intro x a ha hx
    rw [Real.sqrt_sq_eq_abs] at hx
    have : 0 ≤ a := by
      rw [hx.symm]
      simp
    rw [abs_eq this, Or.comm] at hx
    exact hx
  · use 1
    use -1
    norm_num
