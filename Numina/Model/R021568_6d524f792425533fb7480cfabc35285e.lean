import Mathlib

theorem algebra_302347 (a b : ℝ) (ha : a ≠ 0) (y : ℝ → ℝ)
    (hy : ∀ x, y x = a * x ^ 3 + a * x ^ 2 + b) :
    (∀ x, -2 / 3 < x ∧ x < 0 → deriv y x < 0) ↔ a > 0 := by
  constructor
  · -- Assume that for all x in (-2/3, 0), deriv y x < 0, prove a > 0
    intro h
    have hf : y = fun x => a * x ^ 3 + a * x ^ 2 + b := by
      funext x
      specialize hy x
      simpa using hy
    have h1 : deriv y (-1 / 2) < 0 := h (-1 / 2) ⟨by norm_num, by norm_num⟩
    have deriv_y : deriv y (-1 / 2) = 3 * a * (-1 / 2) ^ 2 + 2 * a * (-1 / 2) := by
      rw [hf]
      simp [deriv_pow, deriv_const, deriv_add, deriv_mul, mul_comm]
      all_goals norm_num
      <;> ring_nf <;> norm_num
    rw [deriv_y] at h1
    nlinarith
  · -- Assume a > 0, proved that ∀ x, -2/3 < x ∧ x < 0 → deriv y x < 0
    intro ha x hx
    have hf : y = fun x => a * x ^ 3 + a * x ^ 2 + b := by
      funext x
      specialize hy x
      simpa using hy
    have h_deriv : deriv y x = 3 * a * x ^ 2 + 2 * a * x := by
      rw [hf]
      simp [deriv_pow, deriv_const, deriv_add, deriv_mul, mul_comm]
      all_goals field_simp
      <;> ring_nf <;> field_simp
    rw [h_deriv]
    have hx1 : -2 / 3 < x := hx.1
    have hx2 : x < 0 := hx.2
    have h2 : 3 * x + 2 > 0 := by
      nlinarith
    have h3 : 3 * a * x ^ 2 + 2 * a * x < 0 := by
      have h4 : a * x < 0 := by
        apply mul_neg_of_pos_of_neg
        linarith
        linarith
      have h5 : 3 * x + 2 > 0 := by
        nlinarith
      have h6 : a * x * (3 * x + 2) < 0 := by
        apply mul_neg_of_neg_of_pos
        linarith
        linarith
      have h7 : 3 * a * x ^ 2 + 2 * a * x = a * x * (3 * x + 2) := by
        ring
      linarith
    linarith