import Mathlib

theorem algebra_290324 (a b c d e f : ℝ) (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c)
    (hd : d ≠ e) (he : e ≠ f) (hf : f ≠ d) (h1 : ∃! x, a * x ^ 2 + b * x + c = d * x ^ 2 + e * x + f)
    (h2 : ∃! x, a * x ^ 2 + b * x + c = d * x ^ 2 + f * x + e) (h3 : ∃! x, a * x ^ 2 + c * x + b = d * x ^ 2 + e * x + f)
    (h4 : ∃! x, a * x ^ 2 + c * x + b = d * x ^ 2 + f * x + e) (h5 : ∃! x, a * x ^ 2 + d * x + e = b * x ^ 2 + c * x + f)
    (h6 : ∃! x, a * x ^ 2 + d * x + e = b * x ^ 2 + f * x + c) :
    ∃! x, a * x ^ 2 + b * x + c = d * x ^ 2 + e * x + f ∧
    ∃! x, a * x ^ 2 + b * x + c = d * x ^ 2 + f * x + e ∧
    ∃! x, a * x ^ 2 + c * x + b = d * x ^ 2 + e * x + f ∧
    ∃! x, a * x ^ 2 + c * x + b = d * x ^ 2 + f * x + e ∧
    ∃! x, a * x ^ 2 + d * x + e = b * x ^ 2 + c * x + f ∧
    ∃! x, a * x ^ 2 + d * x + e = b * x ^ 2 + f * x + c := by
  aesop