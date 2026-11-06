import Mathlib

open Complex ComplexConjugate Polynomial

theorem algebra_608710 {p : Polynomial ℂ} (hp : ∀ n, p.coeff n ≠ 0) :
  ∀ r, p.eval r = 0 → ‖r‖ ≤ 2 * sSup {‖p.coeff (n - 1) / p.coeff n‖ | n ∈ Finset.Icc 0 (p.natDegree - 1)} := by
  intro r
  intro h1
  have h2 := hp (p.natDegree + 1)
  simp at h2