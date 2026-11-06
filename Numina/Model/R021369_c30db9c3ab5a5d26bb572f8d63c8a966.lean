import Mathlib

theorem algebra_166035 {x y : ℝ} (h₀ : (x - y) * (x ^ 2 + y ^ 2) = 5) (h₁ : (x + y) * (x ^ 2 - y ^ 2) = 9) :
    (x, y) = (2, 1) ∨ (x, y) = (-1, -2) := by
  have eq1 : (x - y) * (x ^ 2 + y ^ 2) = 5 := h₀
  have eq2 : (x - y) * (x + y) ^ 2 = 9 := by
    have h2 : (x + y) * (x ^ 2 - y ^ 2) = (x - y) * (x + y) ^ 2 := by
      ring
    linarith [h₁, h2]
  have eq5 : (x - y) ^ 3 = 1 := by
    nlinarith [sq_nonneg (x - y - 1), sq_nonneg (x + y + 3), sq_nonneg (x - y), sq_nonneg (x + y - 3), sq_nonneg (x^2 - y^2)]
  -- From now that $(x-y)^3 = 1$, prove $x-y = 1$.
  have eq6 : x - y = 1 := by
    have h2 : (x - y) ^ 3 - 1 = 0 := by linarith
    have h3 : (x - y) ^ 3 - 1 = (x - y - 1) * ((x - y) ^ 2 + (x - y) + 1) := by ring
    rw [h3] at h2
    cases' (mul_eq_zero.mp h2) with h4 h5
    · -- Case that $(x - y - 1) = 0$
      linarith 
    · -- Show that the quadratic has no real roots.
      nlinarith [sq_nonneg ((x - y) + 1 / 2)]
  -- Now from eq6: x - y = 1 and eq2: (x - y) * (x + y) ^ 2 = 9
  have eq7 : (x + y) ^ 2 = 9 := by 
    rw [eq6] at eq2 
    nlinarith 
  -- Now from (x + y)^2 = 9, so (x + y) = 3 or -3
  have eq8 : x + y = 3 ∨ x + y = -3 := by
    have h2 : (x + y) ^ 2 - 9 = 0 := by linarith [eq7]
    have h3 : ((x + y) - 3) * ((x + y) + 3) = 0 := by
      linarith 
    cases' (mul_eq_zero.mp h3) with h4 h5
    · 
      left 
      linarith 
    · 
      right 
      linarith 
  cases eq8 with
  | inl h2 =>
    -- x + y = 3 and x - y = 1, solving get x=2,y=1
    have hx1 : x = 2 := by
      nlinarith [eq6, h2]
    have hy1 : y = 1 := by
      nlinarith [eq6, h2]
    left 
    simp [hx1, hy1]
  | inr h2 =>
    -- x + y = -3 and x - y = 1, solving get x=-1,y=-2
    have hx2 : x = -1 := by
      nlinarith [eq6, h2]
    have hy2 : y = -2 := by
      nlinarith [eq6, h2]
    right 
    simp [hx2, hy2]
    <;> linarith