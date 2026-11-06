import Mathlib

theorem inequalities_599716
    (a b c d : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hd : 0 < d) :
    (a^3 + b^3 + c^3) / (a + b + c) +
    (b^3 + c^3 + d^3) / (b + c + d) +
    (c^3 + d^3 + a^3) / (c + d + a) +
    (d^3 + a^3 + b^3) / (d + a + b) ≥
    a^2 + b^2 + c^2 + d^2 := by

  have h1 : ∀ x y z : ℝ, 0 < x → 0 < y → 0 < z → (x^3 + y^3 + z^3) / (x + y + z) ≥ (x^2 + y^2 + z^2) / 3 := by
    intro x y z hx hy hz
    have h1 : 0 < x + y + z := by
      linarith
    have h2 : x^3 + y^3 + z^3 ≥ (x^2 + y^2 + z^2) / 3 * (x + y + z) := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x + y + z), sq_nonneg (x - y + z), sq_nonneg (x + y - z), sq_nonneg (-x + y + z), 
        mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
      ]
    have h3 : (x^3 + y^3 + z^3) / (x + y + z) ≥ (x^2 + y^2 + z^2) / 3 := by 
      apply (le_div_iff₀ h1).mpr
      linarith
    exact h3
  
  have h2 := h1 a b c ha hb hc
  have h3 := h1 b c d hb hc hd
  have h4 := h1 c d a hc hd ha
  have h5 := h1 d a b hd ha hb

  linarith [h2, h3, h4, h5]