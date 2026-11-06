import Mathlib

/- Solve the system in positive numbers:


$$

\begin{cases}x^{y} & =z \\ y^{z} & =x \\ z^{x} & =y\end{cases}

$$
 -/
theorem algebra_200645 {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x ^ y = z) (h2 : y ^ z = x) (h3 : z ^ x = y) :
    x = 1 ∧ y = 1 ∧ z = 1 := by
  have x_cases : x < 1 ∨ x = 1 ∨ 1 < x := lt_trichotomy x 1
  rcases x_cases with lt | eq | gt
  · exfalso
    -- Prove that z < 1
    have one_lt_z : z < 1 := by
      calc
        z = x^y := symm h1
        _ < 1 := Real.rpow_lt_one (by linarith) lt (by linarith)
    -- Prove that y < 1
    have one_lt_y : y < 1 := by
      calc
        y = z^x := symm h3
        _ < 1 := Real.rpow_lt_one (by linarith) one_lt_z (by linarith)
    -- Prove z < y
    have z_lt_y : z < y := by
      calc
        z = z^1 := by simp
        _ < z^x := Real.rpow_lt_rpow_of_exponent_gt (by linarith) one_lt_z lt
        _ = y := h3
    -- Prove y < x
    have y_lt_x : y < x := by
      calc
        y = y^1 := by simp
        _ < y^z := Real.rpow_lt_rpow_of_exponent_gt (by linarith) one_lt_y (by linarith)
        _ = x := h2
    -- Prove z < y
    have x_lt_z : x < z := by
      calc
        x = x^1 := by simp
        _ < x^y := Real.rpow_lt_rpow_of_exponent_gt (by linarith) (by linarith) (by linarith)
        _ = z := h1
    -- Derive a contradiction
    linarith
  -- Consider the case x = 1
  · rw [eq] at h1
    simp at h1
    rw [symm h1] at h3
    simp at h3
    exact ⟨eq, symm h3, symm h1⟩
  -- Consider the case 1 < x
  -- Proof by contradiction
  exfalso
  -- Prove that 1 < z
  have one_lt_z : 1 < z := by
    calc
      1 < x^y := Real.one_lt_rpow gt hy
      _ = z := h1
  -- Prove that 1 < y
  have one_lt_y : 1 < y := by
    calc
      1 < z^x := Real.one_lt_rpow one_lt_z hx
      _ = y := h3
  -- Prove x < z
  have x_lt_z : x < z := by
    calc
      x = x^(1 : ℝ) := by simp
      _ < x^y := Real.rpow_lt_rpow_of_exponent_lt gt one_lt_y
      _ = z := h1
  -- Prove z < y
  have z_lt_y : z < y := by
    calc
      z = z^(1 : ℝ) := by simp
      _ < z^x := Real.rpow_lt_rpow_of_exponent_lt one_lt_z gt
      _ = y := h3
  -- Prove y < x
  have y_lt_x : y < x := by
    calc
      y = y^(1 : ℝ) := by simp
      _ < y^z := Real.rpow_lt_rpow_of_exponent_lt one_lt_y one_lt_z
      _ = x := h2
  -- Derive a contradiction
  linarith