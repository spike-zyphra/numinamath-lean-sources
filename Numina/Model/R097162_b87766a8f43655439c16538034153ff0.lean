import Mathlib

theorem algebra_10178 {x y : ℝ} (hx : x ^ 2 + 1 = 3 * x) (hy : y ^ 2 + 1 = 3 * y) (hxy : x ≠ y) :
    1 / x ^ 2 + 1 / y ^ 2 = 7 := by
  have h1 : x - y ≠ 0 := by
    exact sub_ne_zero.mpr hxy
  have h2 : x + y = 3 := by
    have eq1 : x ^ 2 - y ^ 2 = 3 * (x - y) := by
      nlinarith [hx, hy]
    have h3 : (x - y) * (x + y) = 3 * (x - y) := by
      linarith [eq1]
    have h4 : (x - y) ≠ 0 := h1
    have h5 : x + y = 3 := by
      apply (mul_left_inj' h4).mp
      linarith
    exact h5
  have h3 : x * y = 1 := by
    have h4 : x ^ 2 + y ^ 2 = 7 := by
      nlinarith [hx, hy, h2]
    nlinarith [h2, h4]
  have hxne0 : x ≠ 0 := by
    intro h
    have hx' : x = 0 := by linarith
    rw [hx'] at hx
    nlinarith
  have hyne0 : y ≠ 0 := by
    intro h
    have hy' : y = 0 := by linarith
    rw [hy'] at hy
    nlinarith
  have h4 : 1 / x ^ 2 + 1 / y ^ 2 = 7 := by
    have h5 : x ^ 2 * y ^ 2 = 1 := by
      calc
        x ^ 2 * y ^ 2 = (x * y) ^ 2 := by ring
        _ = 1 ^ 2 := by rw [h3]
        _ = 1 := by norm_num
    have h6 : x ^ 2 + y ^ 2 = 7 := by
      nlinarith [hx, hy, h2]
    field_simp [hxne0, hyne0]
    nlinarith [h5, h6]
  exact h4