import Mathlib

theorem algebra_192481 (n : ℤ) (h : ∃ a b c : ℤ, a^2 + b^2 + c^2 - a * b - b * c - c * a = n) :
    ∃ d e : ℤ, d^2 + e^2 - d * e = n := by
    rcases h with ⟨a, b, c, h_eq⟩
    use a - b, c - b
    linarith [h_eq, sq_nonneg (a - b - (c - b)), sq_nonneg (a - c)]