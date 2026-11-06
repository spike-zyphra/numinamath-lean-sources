import Mathlib

open Real

theorem inequalities_600230 (x y z : ℝ) (h : x^2 + y^2 + z^2 ≤ 2) :
    ((x ≥ 0 ∨ y ≥ 0 ∨ z ≥ 0) → 2 * x * y * z + 1 ≥ y * z + z * x + x * y) ∧
    (y * z + z * x + x * y + 3 ≥ 2 * (x + y + z)) := by
  constructor
  · -- Prove the first inequality
    intro h1
    rcases h1 with (h1 | h1 | h1)
    · -- Case x ≥ 0
      have hx1 : x ≥ 0 := h1
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x + y + z - 2), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
        h, h1
      ]
    · -- Case y ≥ 0
      have hy1 : y ≥ 0 := h1
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x + y + z - 2), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
        h, h1
      ]
    · -- Case z ≥ 0
      have hz1 : z ≥ 0 := h1
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x + y + z - 2), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
        h, h1
      ]
  · -- Prove the second inequality
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x + y + z - 2), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
      h
    ]