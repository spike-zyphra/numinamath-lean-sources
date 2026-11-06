import Mathlib

theorem algebra_327863 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hne : a + b + c ≠ 0) (h1 : (a + b - c)/c = (a - b + c)/b) (h2 : (a - b + c)/b = (-a + b + c)/a) :
    ((a + b)*(b + c)*(c + a))/(a * b * c) = 8 := by
  have eq1 : b * (a + b - c) = c * (a - b + c) := by
    have h1' : (a + b - c)/c = (a - b + c)/b := h1
    field_simp [hc, hb] at h1' ⊢
    linarith
  have eq3 : (a + b + c) * (b - c) = 0 := by
    nlinarith
  have eq4 : b - c = 0 := by
    cases (mul_eq_zero.mp eq3) with
    | inl h =>
      exfalso
      apply hne
      linarith
    | inr h =>
      linarith
  have beq : b = c := by linarith
  have eq2 : a * (a - b + c) = b * (-a + b + c) := by
    have h2' : (a - b + c)/b = (-a + b + c)/a := h2
    field_simp [hb, ha] at h2' ⊢
    linarith
  have eq5 : (a - b) * (a + b + c) = 0 := by
    nlinarith [eq2, beq]
  have eq6 : a - b = 0 := by
    cases (mul_eq_zero.mp eq5) with
    | inl h =>
      linarith
    | inr h =>
      exfalso
      apply hne
      linarith
  have aeq : a = b := by linarith
  have ceq : c = a := by linarith [aeq, beq]
  have : (a + b) * (b + c) * (c + a) = 8 * (a * b * c) := by
    rw [show b = a by linarith [aeq, beq], show c = a by linarith [aeq, beq]]
    have h3 : (a + a) * (a + a) * (a + a) = 8 * (a * a * a) := by
      ring_nf
    nlinarith [h3]
  have : a * b * c ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    exact ha
    exact hb
    exact hc
  field_simp [this]
  nlinarith [this, eq1, eq2, aeq, beq, ceq]