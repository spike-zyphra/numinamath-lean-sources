import Mathlib

theorem inequalities_39502 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hne : ¬(a = 0 ∧ b = 0 ∧ c = 0)) (f : ℝ → ℝ) (hf : ∀ x, f x = a * x ^ 2 + b * x + c) :
    ∀ x y, f (x * y) ^ 2 ≤ f (x ^ 2) * f (y ^ 2) := by
  intro x y
  have h1 : f (x * y) = a * (x * y) ^ 2 + b * (x * y) + c := hf (x * y)
  have h2 : f (x ^ 2) = a * (x ^ 2) ^ 2 + b * (x ^ 2) + c := hf (x ^ 2)
  have h3 : f (y ^ 2) = a * (y ^ 2) ^ 2 + b * (y ^ 2) + c := hf (y ^ 2)
  rw [h1, h2, h3]
  nlinarith [sq_nonneg (a * x ^ 2 * y ^ 2 - a * x ^ 3 * y ^ 3), sq_nonneg (b * x ^ 2 * y ^ 2 - b * x * y), sq_nonneg (a * x ^ 2 * y ^ 2 - a * (x ^ 2) * (y ^ 2) + a * x ^ 2 * y ^ 2), sq_nonneg (x * y - x ^ 2), sq_nonneg (y * x ^ 2 - x * y ^ 2), sq_nonneg (x * y - x * y), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y - c / b), sq_nonneg (x * y - x * y), sq_nonneg (x - y),
          mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc, sq_nonneg (x * y), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y)]