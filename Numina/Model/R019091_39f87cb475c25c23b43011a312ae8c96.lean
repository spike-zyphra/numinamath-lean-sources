import Mathlib

theorem algebra_30618 {a b c d : ℝ} (h1 : ∀ x, x^2 + a * x + b = (x - a) * (x - c)) (h2 : ∀ x, x^2 + c * x + d = (x - b) * (x - d)) :
    (a, b, c, d) = (-1, -2, 2, 0) ∨ (a, b, c, d) = (0, 0, 0, 0) := by
  have eq1 := h1 0
  have eq2 := h1 1
  have eq3 := h1 2
  have eq4 := h2 0
  have eq5 := h2 1
  have eq6 := h2 2
  ring_nf at eq1 eq2 eq3 eq4 eq5 eq6
  have h3 : c = -2 * a := by
    nlinarith
  have h4 : b = -2 * a^2 := by
    rw [show c = -2 * a by linarith [h3]] at eq1
    nlinarith
  have h5 : d = 2 * a^2 + 2 * a := by
    have eq8 : d = -b - c := by
      nlinarith [eq4, eq5, eq6, h3, h4]
    rw [show b = -2 * a^2 by linarith [h4], show c = -2 * a by linarith [h3]] at eq8
    nlinarith
  have h6 : (2 * a^2 + 2 * a) * (-2 * a^2 - 1) = 0 := by
    rw [show d = 2 * a^2 + 2 * a by linarith [h5]] at eq4
    nlinarith [sq_nonneg (a^2), sq_nonneg (a + 1), sq_nonneg (a - 0)]
  cases' (mul_eq_zero.mp h6) with h7 h8
  · -- Case where $2a^2 + 2a = 0$, leading to $a = 0$ or $a = -1$.
    have ha2 : a * (a + 1) = 0 := by
      nlinarith
    have ha3 : a = 0 ∨ a = -1 := by
      cases' (mul_eq_zero.mp ha2) with ha4 ha5
      · left
        linarith
      · right
        linarith
    cases' ha3 with ha0 ha1
    · -- $a = 0$, leading to $(0,0,0,0)$
      have ha0' : a = 0 := ha0
      have hb0 : b = 0 := by
        rw [ha0'] at h4
        nlinarith
      have hc0 : c = 0 := by
        rw [ha0'] at h3
        nlinarith
      have hd0 : d = 0 := by
        rw [ha0'] at h5
        nlinarith
      simp [ha0', hb0, hc0, hd0]
    · -- $a = -1$, leading to $(-1, -2, 2, 0)$
      have ha1' : a = -1 := ha1
      have hb1 : b = -2 := by
        rw [ha1'] at h4
        nlinarith
      have hc1 : c = 2 := by
        rw [ha1'] at h3
        nlinarith
      have hd1 : d = 0 := by
        rw [ha1'] at h5
        nlinarith
      simp [ha1', hb1, hc1, hd1]
  · -- Case where $-2a^2 - 1 = 0$, which is impossible.
    nlinarith [sq_nonneg a, sq_nonneg (a + 1), sq_nonneg (a - 0)]