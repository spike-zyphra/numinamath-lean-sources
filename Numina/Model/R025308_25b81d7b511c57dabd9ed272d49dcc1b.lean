import Mathlib

theorem algebra_180674 {a b c : ℝ} (h1 : a * b + a + b = c) (h2 : b * c + b + c = a)
    (h3 : c * a + c + a = b) :
    a = 0 ∨ a = -1 ∨ a = -2 := by
  have eq1 : (b + 2) * (c - a) = 0 := by
    nlinarith
  have eq2 : (c + 2) * (a - b) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp eq1) with h4 h5
  · -- Case where b = -2
    have hb : b = -2 := by linarith
    have eq3 : a = -c - 2 := by
      rw [hb] at h2
      nlinarith
    have eq4 : -c ^ 2 - 2 * c = 0 := by
      rw [eq3] at h3
      nlinarith [hb]
    have eq5 : c * (c + 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq5) with h6 h7
    · -- Case where c = 0
      have hc0 : c = 0 := by linarith
      have ha0 : a = -2 := by
        rw [hc0] at eq3
        linarith
      right
      right
      linarith
    · -- Case where c = -2
      have hc2 : c = -2 := by linarith
      have ha0 : a = 0 := by
        rw [hc2] at eq3
        linarith
      left
      linarith
  · -- Case where c = a
    have hc : c = a := by linarith
    cases' (mul_eq_zero.mp eq2) with h8 h9
    · -- Case where c = -2
      have hc2 : c = -2 := by linarith
      have ha2 : a = -2 := by
        linarith [hc2, hc]
      right
      right
      linarith
    · -- Case where a = b
      have ha : a = b := by linarith
      have hc' : c = a := by linarith [hc]
      have h10 : a * a + a + a = a := by
        have h11 : a * b + a + b = c := h1
        rw [show b = a by linarith [ha]] at h11
        rw [show c = a by linarith [hc, ha]] at h11
        nlinarith
      have h11 : a * (a + 1) = 0 := by
        nlinarith [h10, ha, hc]
      cases' (mul_eq_zero.mp h11) with h12 h13
      · -- Case where a = 0
        left
        linarith
      · -- Case where a + 1 = 0
        right
        left
        linarith