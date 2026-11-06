import Mathlib

/- Given that the two roots of the quadratic equation ${{x}^{2}}+px+2=0$ with respect to $x$ are ${{x}_{1}}$ and ${{x}_{2}}$, and ${{x}_{1}}-{{x}_{2}}=2\sqrt{2}$, then the value of $p$ is ___          ___. -/
theorem algebra_971 {p : ℝ} (h : ∃ x1 x2, x1^2 + p * x1 + 2 = 0 ∧ x2^2 + p * x2 + 2 = 0 ∧ x1 - x2 = 2 * √2) :
    p = 4 ∨ p = -4 := by
  rcases h with ⟨x1, x2, h1, h2, h3⟩
  have eq3 : (x1 - x2)^2 = 8 := by
    calc
      (x1 - x2)^2 = (2 * Real.sqrt 2)^2 := by rw [h3]
      _ = 4 * (Real.sqrt 2)^2 := by ring_nf
      _ = 4 * 2 := by rw [Real.sq_sqrt]; positivity
      _ = 8 := by norm_num
  have eq4 : (x1 - x2) * (x1 + x2 + p) = 0 := by
    nlinarith [h1, h2]
  have eq5 : p = - (x1 + x2) := by
    have h4 : x1 - x2 ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), h3]
    have eq4' : x1 + x2 + p = 0 := by
      apply (mul_right_inj' h4).mp
      linarith
    linarith
  -- Derive that x1 * x2 = 2
  have eq6 : x1 * x2 = 2 := by
    have eq1 : x1^2 + x2^2 + p * (x1 + x2) + 4 = 0 := by
      nlinarith [h1, h2]
    rw [eq5] at eq1
    nlinarith [sq_pos_of_pos (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2)]
  have eq7 : (x1 + x2) ^ 2 = 16 := by
    nlinarith [eq6, eq3]
  have eq8 : x1 + x2 = 4 ∨ x1 + x2 = -4 := by
    have h9 : (x1 + x2)^2 = 16 := eq7
    have h10 : (x1 + x2) = 4 ∨ (x1 + x2) = -4 := by
      have h11 : (x1 + x2) ^2 - (16 : ℝ) = 0 := by linarith
      have h13 : (x1 + x2 - 4) * (x1 + x2 + 4) = 0 := by
        linarith
      cases (mul_eq_zero.mp h13) with
      | inl h14 => 
        left
        linarith
      | inr h15 => 
        right
        linarith
    tauto
  cases eq8 with
  | inl h10 =>
    have hp : p = -4 := by
      rw [eq5]
      linarith
    right
    linarith [hp]
  | inr h10 =>
    have hp : p = 4 := by
      rw [eq5]
      linarith
    left
    linarith [hp]