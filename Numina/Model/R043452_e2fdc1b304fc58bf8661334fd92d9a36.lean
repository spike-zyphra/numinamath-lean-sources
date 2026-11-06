import Mathlib

theorem inequalities_89499 (a : ℝ) (ha : 0 < a ∧ a < 1)
    (f g : ℝ → ℝ)
    (hf : ∀ x, f x = a * x ^ 3 + (1 - 4 * a) * x ^ 2 + (5 * a - 1) * x - 5 * a + 3)
    (hg : ∀ x, g x = (1 - a) * x ^ 3 - x ^ 2 + (2 - a) * x - 3 * a - 1) :
    ∀ x, max (|f x|) (|g x|) ≥ a + 1 := by
  rcases ha with ⟨ha0, ha1⟩
  intro x 
  by_contra h
  push_neg at h
  have h1 : |f x| < a + 1 := by 
    cases max_cases (|f x|) (|g x|) with
    | inl h2 =>
      linarith [abs_nonneg (f x), abs_nonneg (g x), h2]
    | inr h2 =>
      linarith [abs_nonneg (f x), abs_nonneg (g x), h2]
  have h2 : |g x| < a + 1 := by 
    cases max_cases (|f x|) (|g x|) with
    | inl h11 =>
      linarith [abs_nonneg (f x), abs_nonneg (g x), h11]
    | inr h11 =>
      linarith [abs_nonneg (f x), abs_nonneg (g x), h11]
  have h3 : - (a + 1) < f x := by 
    linarith [abs_lt.mp h1]
  have h4 : f x < a + 1 := by 
    linarith [abs_lt.mp h1]
  have h5 : - (a + 1) < g x := by 
    linarith [abs_lt.mp h2]
  have h6 : g x < a + 1 := by 
    linarith [abs_lt.mp h2]
  have h7 : f x = a * x ^ 3 + (1 - 4 * a) * x ^ 2 + (5 * a - 1) * x - 5 * a + 3 := hf x
  have h8 : g x = (1 - a) * x ^ 3 - x ^ 2 + (2 - a) * x - 3 * a - 1 := hg x
  rw [h7] at h3 h4
  rw [h8] at h5 h6
  by_cases h10 : x ≤ -2
  · -- Case x ≤ -2
    nlinarith [sq_nonneg (x + 2), sq_nonneg (x - 1), sq_nonneg (x * (x + 1)), sq_nonneg ((x + 2) * (x - 1)), sq_nonneg ((x + 1) * (x - 1)), sq_nonneg (x ^ 2 - 4), mul_pos ha0 (show 0 < 1 - a by linarith), sq_nonneg (x^3), sq_nonneg ((x+1)^2)]
  by_cases h11 : x ≤ -1
  · -- Case -1 ≤ x ≤ -1
    nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x * (x + 1)), sq_nonneg ((x + 2) * (x - 1)), sq_nonneg ((x + 1) * (x - 1)), sq_nonneg (x ^ 2 - 1), mul_pos ha0 (show 0 < 1 - a by linarith), sq_nonneg (x^3), sq_nonneg ((x+1)^2)]
  by_cases h12 : x ≤ 0
  · -- Case -1 < x ≤ 0
    nlinarith [sq_nonneg (x), sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x * (x + 1)), sq_nonneg ((x + 1) * (x - 1)), sq_nonneg (x ^ 2 - 1), mul_pos ha0 (show 0 < 1 - a by linarith), sq_nonneg (x^3), sq_nonneg ((x+1)^2)]
  by_cases h13 : x ≤ 1
  · -- Case 0 < x ≤ 1
    nlinarith [sq_nonneg (x - 1), sq_nonneg (x), sq_nonneg (x + 1), sq_nonneg (x * (x - 1)), sq_nonneg ((x + 1) * (x - 1)), sq_nonneg (x ^ 2 - 1), mul_pos ha0 (show 0 < 1 - a by linarith), sq_nonneg (x^3), sq_nonneg ((x-1)^2)]
  · -- Case x > 1
    nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x * (x - 1)), sq_nonneg ((x + 1) * (x - 1)), sq_nonneg ((x - 1) * (x)), sq_nonneg (x ^ 2 - 4), mul_pos ha0 (show 0 < 1 - a by linarith), sq_nonneg (x^3), sq_nonneg ((x+1)^2)]