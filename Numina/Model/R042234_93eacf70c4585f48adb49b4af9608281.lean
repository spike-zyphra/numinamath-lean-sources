import Mathlib

theorem algebra_303677 {a : ℤ} (ha : a ≠ 0) (h : ∃ x y : ℤ, x ≠ y ∧ x^2 + (a - 6)*x + a = 0 ∧ y^2 + (a - 6)*y + a = 0) :
    a = 16 := by
  rcases h with ⟨x, y, hxy, hx, hy⟩
  have h3 : (x - y) * (x + y + a - 6) = 0 := by
    ring_nf at hx hy ⊢
    nlinarith
  cases' (mul_eq_zero.mp h3) with h3 h3
  · -- x - y = 0 
    exfalso
    apply hxy
    linarith
  · -- x + y + a - 6 = 0
    have h4 : x + y + a - 6 = 0 := by linarith
    have h5 : x * y = a := by
      nlinarith [sq_pos_of_ne_zero (show (x - y) ≠ 0 by
        intro h'
        apply hxy
        linarith), sq_nonneg (x - y), sq_nonneg (x + y - (6 - a)), sq_pos_of_ne_zero ha]
    have h9 : (x + 1) * (y + 1) = 7 := by 
      nlinarith
    have h10 : x + 1 = 1 ∨ x + 1 = 7 ∨ x + 1 = -1 ∨ x + 1 = -7 := by
      have h11 : (x + 1) ∣ 7 := by
        use y + 1
        all_goals linarith
      have h12 : (x + 1) ≤ 7 := by
        apply Int.le_of_dvd (by norm_num) h11
      have h13 : (x + 1) ≥ -7 := by
        have h14 : - (x + 1) ∣ 7 := by 
          exact Int.neg_dvd.2 h11
        have h15 : - (x + 1) ≤ 7 := by
          apply Int.le_of_dvd (by norm_num) h14
        omega
      interval_cases (x + 1) <;> tauto
    rcases h10 with h10 | h10 | h10 | h10
    · -- x + 1 = 1, so x = 0
      have hx0 : x = 0 := by
        linarith
      have hy6 : y = 6 := by
        nlinarith [h10, hx0]
      rw [hx0, hy6] at h5 h4
      have ha0 : a = 0 := by
        linarith
      contradiction
    · -- x + 1 = 7, so x = 6
      have hx6 : x = 6 := by
        linarith
      have hy0 : y = 0 := by
        nlinarith [h10, hx6]
      rw [hx6, hy0] at h5 h4
      have ha0 : a = 0 := by
        linarith
      contradiction
    · -- x + 1 = -1, so x = -2
      have hx2 : x = -2 := by
        linarith
      have hy8 : y = -8 := by
        nlinarith [h10, hx2]
      rw [hx2, hy8] at h5
      linarith
    · -- x + 1 = -7, so x = -8
      have hx8 : x = -8 := by
        linarith
      have hy2 : y = -2 := by
        nlinarith [h10, hx8]
      rw [hx8, hy2] at h5
      linarith