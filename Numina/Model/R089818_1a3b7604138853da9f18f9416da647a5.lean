import Mathlib

theorem algebra_5302 (x : ℝ) (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) (h : Real.sin x + Real.cos x = 10 / 7) :
Real.sin x * Real.cos x = 51 / 98 := by
  have h1 : 0 < x := hx.1
  have h2 : x < Real.pi / 2 := hx.2
  
  have h_sq : (Real.sin x + Real.cos x) ^ 2 = 100 / 49 := by
    rw [h]
    norm_num

  have h_id : (Real.sin x + Real.cos x) ^ 2 = Real.sin x ^ 2 + Real.cos x ^ 2 + 2 * (Real.sin x * Real.cos x) := by
    ring
  
  have h_pythagorean : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq x
  
  -- Now, derive the equation from the squared value and the Pythagorean identity
  -- $(\sin x + \cos x)^2 = \sin^2 x + \cos^2 x + 2 \sin x \cos x = 1 + 2 \sin x \cos x$
  have eq1 : Real.sin x ^ 2 + Real.cos x ^ 2 + 2 * (Real.sin x * Real.cos x) = 100 / 49 := by
    nlinarith [h_id, h_sq, h_pythagorean]

  -- Since $\sin^2 x + \cos^2 x = 1$, substitute to get $1 + 2 \sin x \cos x = \frac{100}{49}$
  -- Therefore $2 \sin x \cos x = \frac{100}{49} - 1 = \frac{51}{49}$
  have eq3 : 2 * (Real.sin x * Real.cos x) = 51 / 49 := by
    nlinarith [eq1, h_pythagorean]

  -- Therefore $\sin x \cos x = \frac{51}{98}$
  linarith