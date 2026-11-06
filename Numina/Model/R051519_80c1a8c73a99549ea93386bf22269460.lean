import Mathlib

theorem algebra_255967 {x y z : ℝ} 
  (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
  (h1 : x + 1 / y = y + 1 / x) (h2 : y + 1 / z = z + 1 / y) (h3 : z + 1 / x = x + 1 / z) :
  x = y ∨ y = z ∨ x = z := by
  have eq1 : (x - y) * (x * y + 1) = 0 := by
    have h11 : x + 1 / y = y + 1 / x := h1
    field_simp [hy, hx] at h11 ⊢
    nlinarith
  have eq2 : (y - z) * (y * z + 1) = 0 := by
    have h22 : y + 1 / z = z + 1 / y := h2
    field_simp [hz, hy] at h22 ⊢ 
    nlinarith
  have eq3 : (z - x) * (z * x + 1) = 0 := by
    have h33 : z + 1 / x = x + 1 / z := h3
    field_simp [hx, hz] at h33 ⊢ 
    nlinarith
  cases' (mul_eq_zero.mp eq1) with h1a h1b
  · -- Case where $x - y = 0$, so $x = y$
    left
    linarith
  · -- Case where $x * y + 1 = 0$, so $x * y = -1$
    have h1b1 : x * y = -1 := by linarith 
    cases' (mul_eq_zero.mp eq2) with h2a h2b
    · -- Case where $y - z = 0$, so $y = z$
      right 
      left 
      linarith 
    · -- Case where $y * z + 1 = 0$, so $y * z = -1$
      have h2b1 : y * z = -1 := by linarith 
      cases' (mul_eq_zero.mp eq3) with h3a h3b
      · -- Case where $z - x = 0$, so $z = x$
        right 
        right 
        linarith 
      · -- Case where $z * x + 1 = 0$, so $z * x = -1$
        have h3b1 : z * x = -1 := by linarith 
        -- From $x * y = -1$ and $y * z = -1$, since $y ≠ 0$
        have h6 : x = z := by 
          have h7 : x * y = y * z := by 
            nlinarith 
          have h9 : x = z := by 
            apply (mul_left_inj' hy).mp 
            linarith 
          exact h9 
        -- This leads to a contradiction as $x^2 = -1$
        have h10 : x * z = x ^ 2 := by 
          rw [show z = x by linarith [h6]] 
          ring 
        have h11 : x ^ 2 = -1 := by 
          nlinarith 
        -- But $x^2 = -1$ is impossible as $x$ is real
        have h12 : x ^ 2 ≥ 0 := sq_nonneg x 
        linarith [h11, h12]