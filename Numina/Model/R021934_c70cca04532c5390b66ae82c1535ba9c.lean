import Mathlib

theorem algebra_7592
    {a b c k : ℝ} (hpos : k > 0 ∧ a > 0 ∧ b > 0 ∧ c > 0) (h1 : a * b = k * a - b) (h2 : b * c = k * b - c) (h3 : c * a = k * c - a) :
    a = b ∧ b = c := by
  rcases hpos with ⟨hk, ha, hb, hc⟩
  have h4 : a = b := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
    ]
  have h5 : b = c := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
    ]
  constructor
  · -- Prove a = b
    exact h4
  · -- Prove b = c
    exact h5