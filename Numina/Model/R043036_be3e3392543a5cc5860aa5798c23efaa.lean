import Mathlib

theorem algebra_267365 (f : ℝ → ℝ) (hf : ∀ x > 0, f x > 0)
    (h : ∀ x y, x > 0 → y > 0 → x^2 * (f x + f y) = (x + y) * f (f x * y)) :
    ∀ x > 0, f x = 1 / x := by

  have h3 : f 1 = 1 := by
    have eq1 := h 1 1 (by norm_num) (by norm_num)
    norm_num at eq1
    have hf1 : f 1 > 0 := hf 1 (by norm_num)
    have eq3 := h (f 1) 1 (by linarith [hf1]) (by norm_num)
    simp [show f (f 1) = f 1 by nlinarith [eq1]] at eq3
    have h4 : f 1 * (2 * (f 1) ^ 2 - f 1 - 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- Case $f(1) = 0$ which is a contradiction as $f 1 > 0$.
      linarith [hf 1 (by norm_num)]
    · -- Now solve the quadratic.
      have h7 : 2 * (f 1) ^ 2 - f 1 - 1 = 0 := by
        linarith
      have hf7 : (f 1 - 1) * (2 * f 1 + 1) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp hf7) with hf8 hf9
      · linarith
      · -- Contradiction $2f 1 + 1 = 0$
        nlinarith [hf 1 (by norm_num)]
  
  intro x hx

  have eq6 := h 1 x (by norm_num) hx
  simp [h3] at eq6

  have eq7 : x * (f x) = 1 := by
    nlinarith [hf x hx]

  have hf8 : f x > 0 := hf x hx
  have h9 : f x = 1 / x := by
    field_simp at eq7 ⊢
    nlinarith [hf8, eq7]
  exact h9