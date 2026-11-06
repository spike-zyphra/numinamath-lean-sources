import Mathlib

theorem algebra_107863 {b c : ℝ} (h : ∃ x y, x ≠ y ∧ x^2 + b * x + c = 0 ∧ y^2 + b * y + c = 0)
    (D : ℝ) (hD : D = b^2 - 4 * c) :
    ∃! x, x^2 + b * x + c + (x - Real.sqrt D)^2 + b * (x - Real.sqrt D) + c = 0 := by
  rcases h with ⟨x, y, hxy, hx, hy⟩
  have h1 : D > 0 := by 
    rw [hD]
    have eq1 : x^2 + b * x + c = 0 := by linarith
    have eq2 : y^2 + b * y + c = 0 := by linarith
    have sub : (x^2 + b * x + c) - (y^2 + b * y + c) = 0 := by linarith
    have eq : (x - y) * (x + y + b) = 0 := by
      ring_nf at sub ⊢
      nlinarith
    have h2 : x ≠ y := hxy
    cases' (mul_eq_zero.mp eq) with h3 h4
    · 
      exfalso
      apply hxy
      linarith
    · 
      nlinarith [sq_pos_of_ne_zero (show (x - y) ≠ 0 by 
        intro h'
        apply hxy
        linarith
      ), sq_nonneg (x - y), sq_nonneg (x + y + b)
      ]
  use (-b + Real.sqrt D) / 2
  constructor
  · -- Show that $\frac{-b + \sqrt{D}}{2}$ is indeed a root of the equation.
    nlinarith [Real.sqrt_pos.mpr (show D > 0 by linarith [h1]), Real.sq_sqrt (show 0 ≤ (D : ℝ) by nlinarith [h1]), sq_nonneg (b - Real.sqrt D), sq_nonneg (b + Real.sqrt D), sq_nonneg (x - y), sq_nonneg (x + y + b), sq_pos_of_ne_zero (show (x - y) ≠ 0 by intro h2; apply hxy; linarith)]
  · -- Show that $\frac{-b + \sqrt{D}}{2}$ is a unique root.
    intro z hz
    have eq : z^2 + b * z + c + (z - Real.sqrt D)^2 + b * (z - Real.sqrt D) + c = 0 := by linarith
    have : (z - (-b + Real.sqrt D) / 2) ^ 2 = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show D > 0 by linarith [h1]), Real.sq_sqrt (show 0 ≤ (D : ℝ) by nlinarith [h1]), sq_nonneg (b - Real.sqrt D), sq_nonneg (b + Real.sqrt D), sq_nonneg (z - Real.sqrt D), sq_nonneg (x - y), sq_nonneg (x + y + b), sq_pos_of_ne_zero (show (x - y) ≠ 0 by intro h2; apply hxy; linarith)]
    have : z - (-b + Real.sqrt D) / 2 = 0 := by
      apply pow_eq_zero 
      exact this
    linarith