import Mathlib

theorem algebra_276763 {x : Fin 3 → ℝ} {p q : ℝ} (hx : ∀ i j, x i = x j → i = j)
    (h1 : x 0 ^ 3 + x 0 * p + q = 0) (h2 : x 1 ^ 3 + x 1 * p + q = 0) (h3 : x 2 ^ 3 + x 2 * p + q = 0) :
    x 0 ^ 3 + x 1 ^ 3 + x 2 ^ 3 = 3 * x 0 * x 1 * x 2 := by
  have h4 : x 0 ≠ x 1 := by
    intro heq
    have h01 : (0 : Fin 3) = (1 : Fin 3) := by
      have h0 : x 0 = x 1 := by linarith [heq]
      have h11 : (0 : Fin 3) = (1 : Fin 3) := by
        apply hx 0 1 h0
      exact h11
    simp at h01
  have h5 : x 0 ≠ x 2 := by 
    intro heq
    have h02 : (0 : Fin 3) = (2 : Fin 3) := by
      have h0 : x 0 = x 2 := by linarith [heq]
      have h11 : (0 : Fin 3) = (2 : Fin 3) := by
        apply hx 0 2 h0
      exact h11
    simp at h02
  have h6 : x 1 ≠ x 2 := by
    intro heq
    have h12 : (1 : Fin 3) = (2 : Fin 3) := by
      have h11 : x 1 = x 2 := by linarith [heq]
      have h111 : (1 : Fin 3) = (2 : Fin 3) := by
        apply hx 1 2 h11
      exact h111
    simp at h12
  have eq1 : x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2 + p = 0 := by
    have eq2 : x 0 ^ 3 + x 0 * p + q = 0 := h1
    have eq3 : x 1 ^ 3 + x 1 * p + q = 0 := h2
    have eq4 : x 0 ^ 3 - x 1 ^ 3 + x 0 * p - x 1 * p = 0 := by linarith [eq2, eq3]
    have eq5 : (x 0 - x 1) * (x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2 + p) = 0 := by
      ring_nf at eq4 ⊢
      linarith
    cases (mul_eq_zero.mp eq5) with
    | inl h =>
      exfalso
      have : x 0 = x 1 := by linarith
      contradiction
    | inr h => linarith
  have eq2 : x 0 ^ 2 + x 0 * x 2 + x 2 ^ 2 + p = 0 := by
    have eq3' : x 0 ^ 3 + x 0 * p + q = 0 := h1
    have eq4' : x 2 ^ 3 + x 2 * p + q = 0 := h3
    have eq5' : x 0 ^ 3 - x 2 ^ 3 + x 0 * p - x 2 * p = 0 := by linarith [eq3', eq4']
    have eq6 : (x 0 - x 2) * (x 0 ^ 2 + x 0 * x 2 + x 2 ^ 2 + p) = 0 := by
      ring_nf at eq5' ⊢
      linarith
    cases (mul_eq_zero.mp eq6) with
    | inl h =>
      exfalso
      have : x 0 = x 2 := by linarith
      contradiction
    | inr h => linarith
  have eq3 : x 1 ^ 2 + x 1 * x 2 + x 2 ^ 2 + p = 0 := by
    have eq3' : x 1 ^ 3 + x 1 * p + q = 0 := h2
    have eq4' : x 2 ^ 3 + x 2 * p + q = 0 := h3
    have eq5' : x 1 ^ 3 - x 2 ^ 3 + x 1 * p - x 2 * p = 0 := by linarith [eq3', eq4']
    have eq6 : (x 1 - x 2) * (x 1 ^ 2 + x 1 * x 2 + x 2 ^ 2 + p) = 0 := by
      ring_nf at eq5' ⊢
      linarith
    cases (mul_eq_zero.mp eq6) with
    | inl h =>
      exfalso
      have : x 1 = x 2 := by linarith
      contradiction
    | inr h => linarith
  have eq4 : x 0 + x 1 + x 2 = 0 := by
    have eq5' : x 0 * x 1 + x 1 ^ 2 = x 0 * x 2 + x 2 ^ 2 := by
      nlinarith [eq1, eq2]
    have eq6 : (x 1 - x 2) * (x 0 + x 1 + x 2) = 0 := by
      nlinarith
    cases (mul_eq_zero.mp eq6) with
    | inl h =>
      exfalso
      have : x 1 = x 2 := by linarith
      contradiction
    | inr h => linarith
  have eq5 : x 0 ^ 3 + x 1 ^ 3 + x 2 ^ 3 = 3 * x 0 * x 1 * x 2 := by
    have h7 : x 0 + x 1 + x 2 = 0 := eq4
    have eq8 : x 0 ^ 3 + x 1 ^ 3 + x 2 ^ 3 - 3 * x 0 * x 1 * x 2 = (x 0 + x 1 + x 2) * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 - (x 0 * x 1 + x 0 * x 2 + x 1 * x 2)) := by 
      ring
    rw [h7] at eq8
    linarith
  exact eq5