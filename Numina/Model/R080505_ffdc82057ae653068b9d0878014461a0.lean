import Mathlib

theorem algebra_222713 (p : ℝ) (h : ∃ x y z, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
    x^3-6*p*x^2+5*p*x+88=0 ∧ y^3-6*p*y^2+5*p*y+88=0 ∧ z^3-6*p*z^2+5*p*z+88=0 ∧
    ∃ d, y=x+d ∧ z=y+d) : p=2 := by
  obtain ⟨x, y, z, hxne, hyne, hzne, hx, hy, hz, ⟨d, hyd, hzd⟩⟩ := h
  have hx' : x = y - d := by linarith [hyd]
  have hz' : z = y + d := by linarith [hzd, hyd]
  rw [hx'] at hx
  rw [hz'] at hz
  have eq3 : y = 2 * p := by
    nlinarith [sq_pos_of_ne_zero (show d ≠ 0 by
      by_contra h'
      have : x = y := by
        linarith [hx']
      contradiction
    ), hx, hy, hz]
  rw [eq3] at hy
  have eq4 : 16 * p^3 - 10 * p^2 - 88 = 0 := by
    nlinarith
  have eq5 : (p - 2) * (16 * p^2 + 22 * p + 44) = 0 := by
    nlinarith [eq4]
  cases' (mul_eq_zero.mp eq5) with hp1 hp2
  · 
    linarith
  · 
    have h1 : 16 * p^2 + 22 * p + 44 > 0 := by
      nlinarith [sq_nonneg (p + 11 / 16)]
    nlinarith