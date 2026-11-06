import Mathlib

theorem algebra_14409 (x : ℕ) (hx : x ≤ 100) (h : (31 + 58 + 98 + x + x) / 5 = 1.5 * (x : ℝ)) :
    x = 34 := by
  have h1 : (31 + 58 + 98 + (x : ℝ) + (x : ℝ)) / 5 = 1.5 * (x : ℝ) := by
    exact_mod_cast h
  -- Solving the linear equation $\frac{31 + 58 + 98 + (x : \mathbb{R}) + (x : \mathbb{R})}{5} = 1.5 \cdot (x : \mathbb{R})$
  have h2 : (x : ℝ) = (34 : ℝ) := by
    norm_num at h1
    linarith
  -- Converting the result from $(x : \mathbb{R}) = 34$ to $x = 34$
  have h3 : x = 34 := by
    exact_mod_cast h2
  exact h3