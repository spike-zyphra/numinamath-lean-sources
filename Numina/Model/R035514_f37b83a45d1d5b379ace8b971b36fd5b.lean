import Mathlib

theorem algebra_303399 {a : ℤ} (x₁ x₂ : ℝ) (hx₁ : x₁^2 + (a + 3) * x₁ + 2 * a + 3 = 0)
    (hx₂ : x₂^2 + (a + 3) * x₂ + 2 * a + 3 = 0) (hxp : x₁ > 0) (hxn : x₂ < 0)
    (hxs : |x₁| < |x₂|) : a = -2 := by

  have h1 : |x₁| = x₁ := by
    rw [abs_of_pos hxp]

  have h2 : |x₂| = -x₂ := by
    rw [abs_of_neg hxn]

  rw [h1, h2] at hxs
  have h3 : x₁ * x₂ < 0 := by
    nlinarith [show x₁ > 0 by linarith, show x₂ < 0 by linarith, hxp, hxn]
  have h4 : x₁ * x₂ = (2 * (a : ℝ) + 3) := by
    nlinarith [sq_pos_of_pos (show x₁ - x₂ > 0 by nlinarith [hxp, hxn]), hx₁, hx₂, hxs]
  have h5 : (2 * (a : ℝ) + 3) < 0 := by
    linarith [h4, h3]
  have h6 : a < -1 := by
    by_contra h7
    push_neg at h7
    have : (2 * (a : ℝ) + 3) ≥ 0 := by
      have ha : a ≥ -1 := by omega
      have : (a : ℝ) ≥ (-1 : ℝ) := by exact_mod_cast ha
      nlinarith
    nlinarith [h5, this]
  have h7 : x₁ + x₂ = - ((a + 3 : ℝ)) := by
    have eq1 : x₁^2 + (a + 3) * x₁ + 2 * a + 3 = 0 := hx₁
    have eq2 : x₂^2 + (a + 3) * x₂ + 2 * a + 3 = 0 := hx₂
    have eq3 : x₁^2 - x₂^2 + (a + 3) * (x₁ - x₂) = 0 := by
      nlinarith
    have eq4 : (x₁ - x₂) * (x₁ + x₂ + (a + 3 : ℝ)) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq4) with h8 h9
    · -- x₁ - x₂ = 0, which is a contradiction since x₁ > 0 and x₂ < 0
      exfalso
      have : x₁ = x₂ := by linarith
      nlinarith [hxp, hxn, show x₁ - x₂ > 0 from by linarith]
    · -- x₁ + x₂ + (a + 3 : ℝ) = 0
      nlinarith
  have h8 : (a + 3 : ℝ) > 0 := by
    have h9 : x₁ + x₂ < 0 := by nlinarith
    nlinarith [h9, h7]
  have h9 : a + 3 > 0 := by
    by_contra h9
    push_neg at h9
    have : (a + 3 : ℝ) ≤ 0 := by
      exact_mod_cast (show (a + 3 : ℤ) ≤ 0 by omega)
    nlinarith
  have h10 : a > -3 := by
    omega
  have h11 : a = -2 := by
    omega
  exact_mod_cast h11