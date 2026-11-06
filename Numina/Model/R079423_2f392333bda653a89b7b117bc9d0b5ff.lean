import Mathlib

theorem algebra_244562 {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hroots : ∃ x y, x ≠ y ∧ x^2 - p * x + q = 0 ∧ y^2 - p * y + q = 0 ∧ |x - y| = 1 ∧ x + y = 2) :
    p = 2 ∧ q = 3 / 4 := by
  obtain ⟨x, y, hxy, hx, hy, h_abs, h_sum⟩ := hroots
  have hp_eq : p = 2 := by 
    have h_eq1 : x^2 - p * x + q = 0 := hx
    have h_eq2 : y^2 - p * y + q = 0 := hy
    have h_diff : (x - y) * (x + y - p) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h_diff) with h1 h2
    · -- Case where x - y = 0
      exfalso
      exact hxy (by linarith)
    · -- Case where x + y - p = 0 
      have hp_eq : p = 2 := by linarith [h_sum]
      exact hp_eq 
  have hq_eq : q = 3 / 4 := by 
    have h_eq1 : x^2 - p * x + q = 0 := hx
    rw [show p = 2 by linarith [hp_eq]] at h_eq1
    have h_eq2 : y^2 - p * y + q = 0 := hy
    rw [show p = 2 by linarith [hp_eq]] at h_eq2
    have h3 : (x - y)^2 = 1 := by 
      cases' abs_cases (x - y) with h h
      · -- Case where |x - y| = 1 and x - y ≥ 0
        nlinarith 
      · -- Case where |x - y| = 1 and x - y < 0
        nlinarith 
    have h4 : x * y = 3 / 4 := by 
      nlinarith [h_sum, h3]
    nlinarith [h_eq1, h_eq2, h4]
  exact ⟨hp_eq, hq_eq⟩