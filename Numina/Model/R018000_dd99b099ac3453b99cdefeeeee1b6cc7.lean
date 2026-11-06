import Mathlib

open Real

theorem calculus_124528 {f : ℝ → ℝ} (hf : f = fun x => x ^ 3)
    (A B : ℝ) (hA : A ≠ B) (hB : f B = f A + deriv f A * (B - A)) :
    deriv f B = 4 * deriv f A := by

  have f_eq : ∀ x, f x = x ^ 3 := by
    intro x
    rw [hf]

  have deriv_f : ∀ x, deriv f x = 3 * x ^ 2 := by
    intro x
    rw [hf]
    simp [deriv_pow]

  have fA_eq : f A = A ^ 3 := by
    apply f_eq

  have fB_eq : f B = B ^ 3 := by
    apply f_eq

  have deriv_fA_eq : deriv f A = 3 * A ^ 2 := by
    apply deriv_f

  have deriv_fB_eq : deriv f B = 3 * B ^ 2 := by
    apply deriv_f

  rw [fB_eq, fA_eq, deriv_fA_eq] at hB

  have h1 : B ^ 3 = 3 * A ^ 2 * B - 2 * A ^ 3 := by
    linarith

  have h2 : B ^ 3 - 3 * A ^ 2 * B + 2 * A ^ 3 = 0 := by
    linarith [h1]

  have h3 : (B - A) ^ 2 * (B + 2 * A) = 0 := by
    ring_nf at h2 ⊢
    linarith

  cases' (mul_eq_zero.mp h3) with h4 h5

  · -- (B - A) ^ 2 = 0
    have h6 : (B - A) ^ 2 = 0 := by
      simpa using h4
    have h7 : B - A = 0 := by
      apply pow_eq_zero
      exact h6
    have h8 : B = A := by
      linarith
    have h9 : A = B := by
      linarith [h8]
    contradiction

  · -- B + 2 * A = 0
    have h7 : B = -2 * A := by
      linarith
    rw [deriv_fB_eq, deriv_fA_eq, h7]
    ring_nf