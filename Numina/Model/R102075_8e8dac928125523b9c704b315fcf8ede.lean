import Mathlib

theorem algebra_123912 (m : ℝ) (h : ∃ a b, ∀ x, (6*x^2+16*x+3*m)/6 = (a*x+b)^2) :
    m ∈ Set.Ioo 3 4 := by
  rcases h with ⟨a, b, h_eq⟩
  have h0 := h_eq 0
  have h1 := h_eq 1
  have h2 := h_eq (-1)
  have h_eq1 : m / 2 = b ^ 2 := by
    nlinarith
  have eq1' : (22 + 3 * m) / 6 = (a + b) ^ 2 := by
    nlinarith
  have eq2' : (-10 + 3 * m) / 6 = (b - a) ^ 2 := by
    nlinarith
  have eq3 : m = 32 / 9 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (b), sq_nonneg (a), h_eq1]
  constructor
  · nlinarith [eq3]
  · nlinarith [eq3]