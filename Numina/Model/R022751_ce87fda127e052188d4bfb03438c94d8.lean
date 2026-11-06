import Mathlib

theorem algebra_314758 (n : ℤ) (h : ∃ x y, x ≠ y ∧ x^2-6*x-4*n^2-32*n=0 ∧ y^2-6*y-4*n^2-32*n=0) :
    n=-18 ∨ n=-8 ∨ n=0 ∨ n=10 := by
  rcases h with ⟨x, y, hne, hx, hy⟩
  have h1 : x + y = 6 := by
    have eq2 : x^2 - y^2 - 6 * (x - y) = 0 := by
      nlinarith
    have eq3 : x^2 - y^2 = (x - y) * (x + y) := by 
      ring
    rw [eq3] at eq2
    have hne : x - y ≠ 0 := by
      intro h
      apply hne
      linarith
    have eq4 : x + y = 6 := by
      apply (mul_left_inj' hne).mp
      linarith
    linarith
  have h2 : x * y = -4 * n^2 - 32 * n := by
    nlinarith [sq_pos_of_ne_zero (show (x - y : ℤ) ≠ 0 by
      intro h
      apply hne
      linarith
    ), sq_nonneg (x - y), sq_nonneg (x + y - 6)]
  have h3 : (2 * (n + 4) - (x - 3)) * (2 * (n + 4) + (x - 3)) = 55 := by
    nlinarith [sq_nonneg (x - 3), sq_nonneg (n + 4), h1, h2]
  have h4 : (2 * (n + 4) - (x - 3)) ∣ 55 := by 
    use (2 * (n + 4) + (x - 3))
    all_goals linarith
  have h5 : (2 * (n + 4) - (x - 3)) ≤ 55 := by
    apply Int.le_of_dvd (by norm_num) h4
  have h6 : (2 * (n + 4) - (x - 3)) ≥ -55 := by
    have h7 : (- (2 * (n + 4) - (x - 3)) ) ∣ 55 := by
      exact Int.neg_dvd.2 h4
    have h8 : - (2 * (n + 4) - (x - 3)) ≤ 55 := by
      apply Int.le_of_dvd (by norm_num) h7
    linarith
  interval_cases h7 : (2 * (n + 4) - (x - 3)) <;> omega