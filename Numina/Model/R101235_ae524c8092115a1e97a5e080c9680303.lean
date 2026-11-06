import Mathlib

theorem algebra_469 (x₁ x₂ : ℝ) (hx₁ : 3*x₁^2+33*x₁-12=0) (hx₂ : 3*x₂^2+33*x₂-12=0)
    (h : x₁≠x₂) : x₁^2+x₂^2=129 := by
  have eq1 : 3 * x₁^2 + 33 * x₁ - 12 = 0 := hx₁
  have eq2 : 3 * x₂^2 + 33 * x₂ - 12 = 0 := hx₂
  have eq3 : 3 * x₁^2 + 33 * x₁ - 12 - (3 * x₂^2 + 33 * x₂ - 12) = 0 := by
    linarith
  have eq4 : 3 * (x₁^2 - x₂^2) + 33 * (x₁ - x₂) = 0 := by
    nlinarith
  have eq5 : (x₁ - x₂) * (3 * (x₁ + x₂) + 33) = 0 := by
    ring_nf at eq4 ⊢
    linarith
  cases (mul_eq_zero.mp eq5) with
  | inl h1 =>
    exfalso
    apply h
    linarith
  | inr h2 =>
    have h3 : x₁ + x₂ = -11 := by
      linarith
    have eq6 : 3 * x₁^2 + 33 * x₁ - 12 = 0 := hx₁
    have eq7 : 3 * x₂^2 + 33 * x₂ - 12 = 0 := hx₂
    have eq6' : 3 * x₁^2 = -33 * x₁ + 12 := by linarith
    have eq7' : 3 * x₂^2 = -33 * x₂ + 12 := by linarith
    have eq8 : 3 * (x₁^2 + x₂^2) = -33 * (x₁ + x₂) + 24 := by
      nlinarith [eq6', eq7']
    rw [h3] at eq8
    nlinarith