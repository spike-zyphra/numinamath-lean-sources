import Mathlib

theorem algebra_12212 (a b : ℝ) (ha : abs a ≤ 1) (hb : abs (a + b) ≤ 1) :
    (a + 1) * (b + 1) ∈ Set.Icc (-2) (9 / 4) := by
  have h1 : -1 ≤ a := by linarith [abs_le.mp ha]
  have h2 : a ≤ 1 := by linarith [abs_le.mp ha]
  have h3 : -1 ≤ a + b := by linarith [abs_le.mp hb]
  have h4 : a + b ≤ 1 := by linarith [abs_le.mp hb]
  constructor
  · -- Prove -2 ≤ (a + 1) * (b + 1)
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - 1), sq_nonneg (b + 1),
      sq_nonneg (a + 1), sq_nonneg (b - 1)
    ]
  · -- Prove (a + 1) * (b + 1) ≤ 9 / 4
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - 1), sq_nonneg (b + 1),
      sq_nonneg (a + 1), sq_nonneg (b - 1)
    ]