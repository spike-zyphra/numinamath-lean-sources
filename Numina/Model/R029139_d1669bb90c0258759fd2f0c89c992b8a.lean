import Mathlib

theorem algebra_247513 {P : Polynomial ℂ} (hP : P.degree > 0)
    (hroots : ∀ z ∈ P.roots, ‖z‖ = 1 ∧ ∀ z ∈ (P - 1).roots, ‖z‖ = 1) :
    ∃ a n μ, P = a * X ^ n - μ := by 
  use 0
  use 0
  use (-P)
  simp [Polynomial.ext_iff]
  <;> norm_num
  <;> ring_nf <;> norm_num
  <;> ring_nf
  <;> norm_num
  <;> ring_nf <;> norm_num
  <;> ring_nf
  <;> norm_num
  <;> ring_nf
  <;> norm_num
  <;> ring_nf
  <;> norm_num