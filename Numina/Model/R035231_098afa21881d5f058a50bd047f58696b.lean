import Mathlib
theorem inequalities_607602 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c = 9) :
    9 ≤ (a ^ 3 + b ^ 3) / (a * b + 9) + (b ^ 3 + c ^ 3) / (b * c + 9) + (c ^ 3 + a ^ 3) / (c * a + 9) := by
  have h1 : ∀ x y : ℝ, 0 < x → 0 < y → (x ^ 3 + y ^ 3) / (x * y + 9) ≥ x + y - 3 := by
    intro x y hx hy
    have h2 : 0 < x * y + 9 := by nlinarith
    suffices (x ^ 3 + y ^ 3) ≥ (x + y - 3) * (x * y + 9) by
      apply (le_div_iff₀ h2).mpr
      linarith
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - 3), sq_nonneg (y - 3),
      sq_nonneg (x + y - 3), sq_nonneg (x - y), sq_nonneg (x - 3), sq_nonneg (y - 3),
      mul_pos hx hy
    ]
  have h2 : (a ^ 3 + b ^ 3) / (a * b + 9) ≥ a + b - 3 := h1 a b ha hb
  have h3 : (b ^ 3 + c ^ 3) / (b * c + 9) ≥ b + c - 3 := h1 b c hb hc
  have h4 : (c ^ 3 + a ^ 3) / (c * a + 9) ≥ c + a - 3 := h1 c a hc ha
  have h5 : (a ^ 3 + b ^ 3) / (a * b + 9) + (b ^ 3 + c ^ 3) / (b * c + 9) + (c ^ 3 + a ^ 3) / (c * a + 9) ≥ (a + b - 3) + (b + c - 3) + (c + a - 3) := by
    linarith
  have h6 : (a + b - 3) + (b + c - 3) + (c + a - 3) = 2 * (a + b + c) - 9 := by
    linarith
  have h7 : (a + b - 3) + (b + c - 3) + (c + a - 3) = 9 := by
    rw [h6, h]
    norm_num
  linarith [h5, h7]