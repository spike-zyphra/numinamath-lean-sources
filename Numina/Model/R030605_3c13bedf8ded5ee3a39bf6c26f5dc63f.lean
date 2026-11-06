import Mathlib

theorem algebra_209118 (x y : ℝ) (hx : x ≠ 1) (hy : y ≠ 1)
    (hxy : x + y = 1) :
    x / (y^3 - 1) + y / (1 - x^3) + 2 * (x - y) / (x^2 * y^2 + 3) = 0 := by 
  have h1 : y = 1 - x := by linarith
  rw [h1]
  have h2 : x ≠ 1 := hx
  have h3 : (1 - x) ≠ 1 := by
    intro h
    apply hy
    have h7 : (1 - x) = 1 := by linarith
    have h8 : x = 0 := by linarith
    have h9 : y = 1 := by
      rw [show y = 1 - x by linarith]
      nlinarith
    tauto
  -- Need to show $1 - x ≠ 0$, so $x ≠ 1$, which is given by hx
  have h4 : (1 - x) ≠ 0 := by 
    intro h
    have hx0 : x = 1 := by
      nlinarith
    tauto
  -- Show that $(1 - x) ^ 3 - 1 ≠ 0$, which implies x ≠ 0
  have h5 : (1 - x) ^ 3 - 1 ≠ 0 := by
    by_contra h
    have hx0 : x = 0 := by
      have h8 : (1 - x) ^ 3 = 1 := by linarith
      have h9 : (1 - x) = 1 := by
        have h2 : (1 - x) ^ 3 - 1 = 0 := by linarith
        have h10 : (1 - x - 1) * ((1 - x) ^ 2 + (1 - x) + 1) = 0 := by
          ring_nf at h2 ⊢
          <;> nlinarith
        cases' (mul_eq_zero.1 h10) with h11 h12
        · -- $1 - x - 1 = 0$
          linarith
        · -- $(1 - x) ^ 2 + (1 - x) + 1 = 0$
          nlinarith [sq_nonneg ((1 - x) + 1 / 2)]
      nlinarith
      all_goals nlinarith
    have h6 : y = 1 := by
      rw [show y = 1 - x by linarith]
      nlinarith
    have h7 : y = 1 := h6
    tauto
  -- Show that $1 - x^3 ≠ 0$, which implies x ≠ 1
  have h6 : 1 - x ^ 3 ≠ 0 := by
    by_contra h
    have hx1 : x = 1 := by
      have h7 : x ^ 3 = 1 := by linarith
      have h8 : x ^ 3 - 1 = 0 := by linarith
      have h9 : (x - 1) * (x ^ 2 + x + 1) = 0 := by
        ring_nf at h8 ⊢
        <;> nlinarith
      cases' (mul_eq_zero.1 h9) with h10 h11
      · -- $x - 1 = 0$
        linarith
      · -- $x^2 + x + 1 = 0$
        nlinarith [sq_nonneg (x + 1 / 2)]
    tauto
  -- Show that $x^2 * (1 - x) ^ 2 + 3 ≠ 0$
  have h7 : x ^ 2 * (1 - x) ^ 2 + 3 ≠ 0 := by
    nlinarith [sq_nonneg (x * (1 - x)), sq_nonneg (x - 1 / 2), sq_nonneg ((1 - x) - 1 / 2), sq_nonneg (x ^ 2), sq_nonneg ((1 - x) ^ 2)]
  field_simp [h5, h6, h7]
  <;> ring_nf <;> nlinarith [sq_nonneg (x - (1 - x)), sq_nonneg (x - 0), sq_nonneg ((1 - x) - 0), sq_nonneg (x * (1 - x)), sq_nonneg (x ^ 2 - (1 - x) ^ 2)]