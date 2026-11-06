import Mathlib

theorem algebra_47041 {r s : ℝ} (P : ℝ → ℝ) (hP : ∀ x, P x = x ^ 2 + r * x + s)
    (hroots : ∃ x y, x ≠ y ∧ P x = 0 ∧ P y = 0 ∧ x < -1 ∧ y < -1 ∧ |x - y| < 2) :
    ∀ x, P (P x) > 0 := by
  rcases hroots with ⟨x1, x2, hx1x2, hPx1, hPx2, hx1, hx2, hx1x22⟩
  have eq1 : x1 ^ 2 + r * x1 + s = 0 := by
    rw [hP x1] at hPx1 
    linarith
  have eq2 : x2 ^ 2 + r * x2 + s = 0 := by
    rw [hP x2] at hPx2 
    linarith
  have eq3 : r = - (x1 + x2) := by
    have eq3 : (x1 + x2 + r) * (x1 - x2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq3) with h1 h2
    · linarith
    · -- x1 - x2 = 0, which contradicts with x1 ≠ x2
      exfalso
      apply hx1x2
      linarith
  have eq4 : s = x1 * x2 := by
    rw [eq3] at eq1
    nlinarith
  intro x
  have eq10 : P (P x) = (P x - x1) * (P x - x2) := by
    rw [hP]
    rw [eq3, eq4]
    ring_nf
    <;> nlinarith [eq1, eq2, hx1x2]
  have eq11 : P x > x1 := by
    rw [hP x]
    rw [eq3, eq4]
    nlinarith [sq_nonneg (x - (x1 + x2) / 2), sq_nonneg (x - x1), sq_nonneg (x - x2), 
      sq_pos_of_ne_zero (show x1 - x2 ≠ 0 by 
        intro h
        apply hx1x2
        linarith 
      ), 
      hx1, hx2, abs_lt.mp hx1x22 
    ]
  have eq12 : P x > x2 := by
    rw [hP x]
    rw [eq3, eq4]
    nlinarith [sq_nonneg (x - (x1 + x2) / 2), sq_nonneg (x - x1), sq_nonneg (x - x2), 
      sq_pos_of_ne_zero (show x1 - x2 ≠ 0 by 
        intro h
        apply hx1x2
        linarith 
      ), 
      hx1, hx2, abs_lt.mp hx1x22 
    ]
  have eq13 : (P x - x1) * (P x - x2) > 0 := by
    have hx14 : P x - x1 > 0 := by 
      linarith [eq11]
    have hx15 : P x - x2 > 0 := by 
      linarith [eq12]
    nlinarith
  rw [eq10]
  linarith [eq13]
  all_goals linarith
  all_goals linarith
  all_goals nlinarith
  all_goals nlinarith