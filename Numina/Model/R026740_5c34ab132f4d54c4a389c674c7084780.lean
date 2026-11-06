import Mathlib

open Real

theorem inequalities_292956 (n : ℕ) (hn : n > 0) (x : ℝ) (hx : n ≤ x) :
    x + n / x ≥ n + 1 ∧ (x + n / x = n + 1 ↔ x = n) := by
  have h1 : (n : ℝ) > (0 : ℝ) := by
    exact_mod_cast hn
  have h2 : x ≥ (n : ℝ) := by
    exact_mod_cast hx
  have h3 : x ≥ (1 : ℝ) := by
    have hn1 : (n : ℝ) ≥ (1 : ℝ) := by
      have h : n ≥ 1 := by linarith
      exact_mod_cast h
    nlinarith
  have h4 : x + (n : ℝ) / x ≥ (n + 1 : ℝ) := by
    have hx_pos : x > (0 : ℝ) := by
      nlinarith
    have h5 : x ^ 2 + (n : ℝ) ≥ (n + 1 : ℝ) * x := by
      nlinarith [sq_nonneg (x - (n : ℝ)), sq_nonneg (x - (1 : ℝ)), h1, h2, h3]
    have hx_ne_zero : x ≠ 0 := by
      nlinarith
    have h6 : x + (n : ℝ) / x ≥ (n + 1 : ℝ) := by
      have h7 : x + (n : ℝ) / x - (n + 1 : ℝ) ≥ 0 := by
        have h8 : x + (n : ℝ) / x - (n + 1 : ℝ) = (x ^ 2 + (n : ℝ) - (n + 1 : ℝ) * x) / x := by
          field_simp
          <;> ring
        rw [h8]
        apply div_nonneg
        linarith
        positivity
      linarith
    linarith
  have h_eq : x + (n : ℝ) / x = (n + 1 : ℝ) ↔ x = (n : ℝ) := by
    constructor
    · -- Assume x + n / x = n + 1, prove x = n
      intro h_eq1
      have hx_pos : x > (0 : ℝ) := by
        nlinarith
      have h7 : x ^ 2 + (n : ℝ) = (n + 1 : ℝ) * x := by
        have h6 : x ≠ 0 := by nlinarith
        field_simp at h_eq1 ⊢
        <;> nlinarith [sq_nonneg (x - (n : ℝ)), sq_nonneg (x - (1 : ℝ)), h1, h2, h3, h6]
      have h8 : (x - (n : ℝ)) * (x - (1 : ℝ)) = 0 := by
        nlinarith [h7, sq_nonneg (x - (n : ℝ)), sq_nonneg (x - (1 : ℝ)), h1, h2, h3]
      cases' (mul_eq_zero.mp h8) with h9 h10
      · -- Case where $x - n = 0$, so $x = n$
        linarith
      · -- Case where $x - 1 = 0$, so $x = 1$
        have hx1 : x = (n : ℝ) := by
          have h6 : (n : ℝ) ≤ (1 : ℝ) := by
            nlinarith [show (n : ℝ) ≤ (1 : ℝ) from by nlinarith [show (x : ℝ) = (1 : ℝ) by linarith [h10], h2]]
          have h7 : (n : ℝ) ≥ (1 : ℝ) := by
            have : n ≥ 1 := by omega
            exact_mod_cast this
          have hn1 : (n : ℝ) = (1 : ℝ) := by
            linarith
          have : (x : ℝ) = (1 : ℝ) := by linarith [h10]
          linarith [this, hn1]
        linarith [hx1]
    · -- Assume x = n, prove x + n / x = n + 1
      intro h_eq2
      rw [h_eq2]
      have h6 : (n : ℝ) ≠ 0 := by
        nlinarith
      field_simp
      <;> nlinarith
  constructor
  · -- First part: show $x + \frac{n}{x} \geq n + 1$
    exact_mod_cast h4
  · -- Second part: show equality holds iff $x = n$
    exact_mod_cast h_eq