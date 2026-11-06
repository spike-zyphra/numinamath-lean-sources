import Mathlib

theorem algebra_82153 {x y z n : ℤ} (h : x * y + y * z + z * x = 3 * n ^ 2 - 1)
    (h' : x + y + z = 3 * n) (h'' : x ≥ y ∧ y ≥ z) :
    x = n + 1 ∧ y = n ∧ z = n - 1 := by 
  have h1 : z = 3 * n - x - y := by 
    linarith 
  rw [show z = 3 * n - x - y by linarith] at h
  have h3 : (x - (n + 1)) * (x - (n - 1)) = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x - n), sq_nonneg (y - n), sq_nonneg (z - n), h'', h']
  have hx1 : x = n + 1 ∨ x = n - 1 := by
    cases (mul_eq_zero.mp h3) with
    | inl h4 =>
      left
      linarith 
    | inr h5 =>
      right
      linarith 
  rcases hx1 with (h4 | h4)
  · 
    have hx1 : x = n + 1 := h4 
    have hy1 : y = n := by 
      nlinarith [sq_nonneg (y - n), h'']
    have hz1 : z = n - 1 := by
      linarith [hx1, hy1, h']
    exact ⟨by linarith, by linarith, by linarith⟩ 
  · 
    -- Case x = n - 1
    have hx1 : x = n - 1 := h4 
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (y - n), sq_nonneg (z - (n - 1)), sq_nonneg (x - (n - 1)), h']