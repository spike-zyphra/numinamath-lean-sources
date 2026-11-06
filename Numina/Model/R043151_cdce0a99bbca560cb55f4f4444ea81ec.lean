import Mathlib

theorem algebra_235138 :
  {(x, y) : ℝ × ℝ | x^4 + (7 / 2) * x^2 * y + 2 * y^3 = 0 ∧ 4 * x^2 + 7 * x * y + 2 * y^3 = 0} =
  {(0, 0), (2, -1), (-11 / 2, -11 / 2)} := by
  ext ⟨x, y⟩
  simp [-one_div]
  constructor
  · -- First direction: from the system of equations to the solutions
    rintro ⟨h₁, h₂⟩
    have eq1 : 2 * x^4 + 7 * x^2 * y + 4 * y^3 = 0 := by
      linarith [h₁]
    have eq2 : 4 * x^3 + 7 * x^2 * y + 2 * x * y^3 = 0 := by
      have eq2' : 4 * x^2 + 7 * x * y + 2 * y^3 = 0 := by linarith [h₂]
      have eq3 : x * (4 * x^2 + 7 * x * y + 2 * y^3) = x * 0 := by rw [eq2']
      nlinarith
    have eq3 : 2 * x^4 - 4 * x^3 + 4 * y^3 - 2 * x * y^3 = 0 := by
      nlinarith
    have eq4 : -2 * (x - 2) * (x - y) * (x^2 + x * y + y^2) = 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (y)]
    cases' (mul_eq_zero.mp eq4) with h3 h4
    cases' (mul_eq_zero.mp h3) with h5 h6
    · -- case $-2(x-2) = 0$, so $x = 2$
      have hx2 : x = 2 := by linarith
      rw [hx2] at h₂
      have hy2 : y = -1 := by
        ring_nf at h₂
        have h_eq : y^3 + 7 * y + 8 = 0 := by nlinarith
        have h_eq2 : (y + 1) * (y^2 - y + 8) = 0 := by
          nlinarith
        cases' (mul_eq_zero.mp h_eq2) with h_eq3 h_eq4
        · -- $y + 1 = 0$
          linarith
        · -- $y^2 - y + 8 = 0$, no real solution
          nlinarith [sq_nonneg (y - 1/2)]
      simp [hx2, hy2]
    · -- case $x - y = 0$, so $x = y$
      have h_eq7 : x = y := by linarith
      rw [show y = x by linarith [h_eq7]] at h₂
      have hy2 : x = 0 ∨ x = -11 / 2 := by
        ring_nf at h₂
        have h_eq8 : x^2 * (11 + 2 * x) = 0 := by linarith
        cases' (mul_eq_zero.mp h_eq8) with h_eq9 h_eq10
        · -- case $x^2 = 0$
          have : x = 0 := by
            nlinarith
          left
          linarith
        · -- case $11 + 2x = 0$
          right
          linarith
      cases' hy2 with h_eq10 h_eq10
      · -- case x = 0
        have hy20 : y = 0 := by linarith [h_eq7, h_eq10]
        simp [h_eq10, hy20]
      · -- case x = -11/2
        have hy20 : y = -11/2 := by linarith [h_eq7, h_eq10]
        simp [h_eq10, hy20]
    · -- case $x^2 + x * y + y^2 = 0$
      have h_eq8 : x^2 + x * y + y^2 = 0 := by nlinarith
      have h_eq9 : y = 0 := by
        nlinarith [sq_nonneg (2 * x + y), sq_nonneg (y)]
      have h_eq10 : x = 0 := by
        rw [h_eq9] at h_eq8
        nlinarith [sq_nonneg x]
      simp [h_eq10, h_eq9]
  · -- Second direction: the solutions satisfy the system.
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- case (0, 0)
      constructor
      · norm_num
      · norm_num
    · -- case (2, -1)
      constructor
      · norm_num
      · norm_num
    · -- case (-11/2, -11/2)
      constructor
      · norm_num
      · norm_num