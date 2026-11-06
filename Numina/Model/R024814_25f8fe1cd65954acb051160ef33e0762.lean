import Mathlib

theorem inequalities_597281
    (a b c : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hc : 0 ≤ c)
    (h1 : a ≤ 1)
    (h2 : 1 ≤ b)
    (h3 : b ≤ c) :
    (a + b + c = 3 → a^2 * b + b^2 * c + c^2 * a ≥ a * b * c + 2) ∧
    (a * b + b * c + c * a = 3 → a^2 * b + b^2 * c + c^2 * a ≥ 3) := by
  constructor
  · -- First implication: If a+b+c=3, prove the inequality.
    intro h_eq
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2),
      mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr (show b ≤ c from h3)),
      mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr (show b ≤ c from h3)),
      mul_nonneg ha (sub_nonneg.mpr h1),
      mul_nonneg ha (sub_nonneg.mpr h2),
      mul_nonneg (sub_nonneg.mpr h2) hc
    ]
  · -- Second implication: If ab+bc+ca=3, prove the inequality.
    intro h_eq
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
      sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2),
      mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr (show b ≤ c from h3)),
      mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr (show b ≤ c from h3)),
      mul_nonneg ha (sub_nonneg.mpr h1),
      mul_nonneg ha (sub_nonneg.mpr h2),
      mul_nonneg (sub_nonneg.mpr h2) hc
    ]