import Mathlib

theorem algebra_136314 {f : ℝ → ℝ}
    (hf : ∀ x, x ≠ 0 ∧ x ≠ 1 ∧ x ≠ -1 → f (x - 1 / x) = x / (x ^ 2 - 1) - x ^ 2 - 1 / x ^ 2) :
    ∀ x, x ≠ 0 → f x = -x ^ 2 + 1 / x - 2 := by
  intro x hx
  have h1 : ∀ x, x ≠ 0 ∧ x ≠ 1 ∧ x ≠ -1 → f (x - 1 / x) = x / (x ^ 2 - 1) - x ^ 2 - 1 / x ^ 2 := hf
  have h2 : ∃ s, s ^ 2 - x * s - 1 = 0 := by 
    use (x + Real.sqrt (x^2 + 4)) / 2
    nlinarith [Real.sqrt_nonneg (x ^ 2 + 4), Real.sq_sqrt (show x ^ 2 + 4 ≥ 0 by nlinarith)]
  rcases h2 with ⟨s, hs⟩
  have hs1 : s ≠ 0 := by 
    by_contra h
    rw [h] at hs
    nlinarith
  have hs2 : s ≠ 1 := by
    by_contra h 
    have h1' : x = (0 : ℝ) := by 
      nlinarith [hs, h]
    have h0 : x = 0 := by linarith
    contradiction 
  have hs3 : s ≠ -1 := by 
    by_contra h
    have h1' : x = (0 : ℝ) := by 
      nlinarith [hs, h]
    have h0 : x = 0 := by linarith
    contradiction 
  have h3 : f (s - 1 / s) = s / (s ^ 2 - 1) - s ^ 2 - 1 / s ^ 2 := h1 s ⟨hs1, hs2, hs3⟩
  have h4 : s - 1 / s = x := by
    field_simp at *
    nlinarith [hs, Real.sqrt_nonneg (x ^ 2 + 4), Real.sq_sqrt (show x ^ 2 + 4 ≥ 0 by nlinarith)]
  rw [show f x = f (s - 1 / s) by rw [h4]] 
  rw [h3]
  have eq1 : s / (s ^ 2 - 1) = 1 / x := by
    have h_eq : s ^ 2 - 1 = x * s := by 
      nlinarith [hs]
    rw [h_eq]
    field_simp [show x ≠ 0 by assumption, show s ≠ 0 by assumption]
    <;> nlinarith 
  have eq3 : s ^ 2 + 1 / s ^ 2 = x ^ 2 + 2 := by
    have eq3a : s ^ 2 + 1 / s ^ 2 = (s - 1 / s) ^ 2 + 2 := by 
      field_simp 
      <;> nlinarith 
    have eq3b : s - 1 / s = x := h4 
    rw [eq3a, eq3b]
    <;> nlinarith 
  rw [eq1]
  field_simp [show x ≠ 0 by assumption, show s ≠ 0 by assumption] at *
  <;> nlinarith [Real.sqrt_nonneg (x ^ 2 + 4), Real.sq_sqrt (show x ^ 2 + 4 ≥ 0 by nlinarith)]