import Mathlib

/-A point $(x,y)$ on the coordinate plane with both coordinates negative is a distance of 6 units from the $x$-axis. It is a distance of 15 units from the point $(8,3)$. It is a distance $\sqrt{n}$ from the origin. What is $n$?-/
theorem algebra_21362 (x y : ℝ) (hx : x < 0) (hy : y < 0)
    (h1 : abs y = 6) (h2 : Real.sqrt ((x - 8)^2 + (y - 3)^2) = 15)
    (n : ℕ) (hn : n > 0) (h3 : Real.sqrt (x^2 + y^2) = Real.sqrt n) :
    n = 52 := by
  -- from h3, we get x^2 + y^2 = n
  have eq : x^2 + y^2 = (√n)^2 := by
    rw [←Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)]
    exact h3
  rw [Real.sq_sqrt (by positivity)] at eq

  -- from h2, we get (x - 8)^2 + (y - 3)^2 = 15^2
  have : (x - 8)^2 + (y - 3)^2 = 15^2 := by
    rw [←Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)]
    exact h2
  norm_cast at this

  -- from h1, we get y = -6
  have hy : y = -6 := by
    rw [abs_eq] at h1
    obtain (r | r) := h1
    all_goals linarith

  -- so, x = 20 or x = -4, but x < 0, so x = -4
  have : x^2 + y^2 = 52 := by
    rw [hy] at this
    have : (x - 20) * (x + 4) = 0 := by
      simp at this
      linarith
    simp at this
    obtain (r | r) := this
    · -- r: x - 20 = 0
      linarith
    · -- r: x + 4 = 0
      have : x = -4 := by linarith
      rw [this, hy]
      ring_nf

  rw [this] at eq
  norm_cast at eq
  exact eq.symm
