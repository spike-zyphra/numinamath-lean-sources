import Mathlib

theorem algebra_293507 {P Q R : Polynomial ℝ} (hP : P^2 + Q^2 = R^2)
    (hPQ : P.degree = 3 ∧ Q.degree = 3) (hQR : R.degree = 2) :
    ∀ x ∈ P.roots, ∃ r : ℝ, x = r ∧ ∀ x ∈ Q.roots, ∃ r : ℝ, x = r := by
  intro x hx
  refine' ⟨x, rfl, fun x hxQ => _⟩
  refine' ⟨x, rfl⟩