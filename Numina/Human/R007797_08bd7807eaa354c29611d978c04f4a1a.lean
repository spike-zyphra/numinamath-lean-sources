import Mathlib

/- If we express $2x^2 + 6x + 11$ in the form $a(x - h)^2 + k$, then what is $h$? -/
theorem algebra_10580 {a h k : ℝ} (ha : a ≠ 0) (h_eq : ∀ x, 2*x^2+6*x+11 = a*(x-h)^2+k) :
    h = -3/2 := by
  -- Differentiate both sides of the equation
  have h_diff : ∀ x, 4*x+6 = 2*a*(x-h) := by
    intro x
    replace h_eq := funext h_eq
    apply_fun (deriv · x) at h_eq
    simp at h_eq
    -- Apply the lemmas of differentiation
    rw [deriv_add, deriv_const_mul, deriv_pow, deriv_const_mul] at h_eq <;> try simp
    . -- Simplify the equation
      simp at h_eq
      linarith
    . -- Apply the lemma of differentiability
      exact DifferentiableAt.mul (by simp) (by simp)

  -- Let $x = -3/2$
  specialize h_diff (-3/2)
  norm_num at h_diff
  simp [ha] at h_diff
  linarith
