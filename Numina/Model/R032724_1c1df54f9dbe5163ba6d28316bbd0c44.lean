import Mathlib

theorem algebra_6413
    {x : ℝ}
    (hx : x ≠ 0)
    (h : x + 1/x = 1) :
    x^(2020) + 1/x^(2020) = -1 := by 
  -- Manipulate the equation to get a polynomial equation
  have h1 : x ^ 2 + 1 = x := by 
    calc 
      x ^ 2 + 1 = x * (x + 1/x) := by 
        field_simp 
        <;> ring 
      _ = x * 1 := by 
        rw [h] 
      _ = x := by 
        ring 
  have h2 : x ^ 2 = x - 1 := by
    linarith 
  -- Now compute x^3
  have h3 : x ^ 3 = -1 := by
    calc 
      x ^ 3 = x * x ^ 2 := by 
        ring 
      _ = x * (x - 1) := by 
        rw [h2]
      _ = x ^ 2 - x := by 
        ring 
      _ = (x - 1) - x := by 
        rw [h2]
      _ = -1 := by 
        linarith 
  -- Now compute x^6
  have h4 : x ^ 6 = 1 := by
    calc 
      x ^ 6 = (x ^ 3) ^ 2 := by 
        ring 
      _ = (-1) ^ 2 := by 
        rw [h3]
      _ = 1 := by 
        norm_num 
  -- Now compute x^4 
  have h5 : x ^ 4 = -x := by
    calc 
      x ^ 4 = x * x ^ 3 := by 
        ring 
      _ = x * (-1) := by 
        rw [h3]
      _ = -x := by 
        ring 
  -- Now compute x^2020
  have h6 : x ^ 2020 = x ^ 4 := by 
    calc
      x ^ 2020 = (x ^ 6) ^ 336 * x ^ 4 := by 
        ring_nf 
      _ = (1) ^ 336 * x ^ 4 := by 
        rw [h4]
      _ = x ^ 4 := by 
        ring 
  -- Make substitutions in $x^2020 + \frac{1}{x^2020}$ 
  have eq10 : x^(2020) + 1/x^(2020) = x^4 + 1/x^4 := by
    rw [show x ^ 2020 = x ^ 4 by linarith [h6]]
    <;> field_simp [hx] at *
    <;> norm_num
  rw [eq10]
  have h7 : x^2 + 1 / x^2 = -1 := by 
    have eq11 : x^2 + 1 / x^2 = (x + 1 / x) ^ 2 - 2 := by 
      field_simp [hx] 
      <;> ring 
    rw [eq11, h] 
    all_goals 
      norm_num 
  have h8 : x^4 + 1 / x^4 = -1 := by 
    have eq12 : x^4 + 1 / x^4 = (x^2 + 1 / x^2) ^ 2 - 2 := by
      field_simp [hx] 
      <;> ring 
    rw [eq12, h7]
    all_goals 
      norm_num 
  linarith [h8]