import Mathlib

theorem algebra_238582 {a b c d : ℝ} (h : a + 5 = b ^ 2 - 1 ∧ b ^ 2 - 1 = c ^ 2 + 3 ∧ c ^ 2 + 3 = d - 4) :
    max (max a b) (max c d) = d := by
  rcases h with ⟨h1, h2, h3⟩
  have h4 : a = c ^ 2 - 2 := by
    have h5 : b ^ 2 = c ^ 2 + 4 := by
      nlinarith
    nlinarith [h1, h5]
  have h5 : d = c ^ 2 + 7 := by
    nlinarith
  have h6 : b ^ 2 = c ^ 2 + 4 := by 
    nlinarith
  have h7 : d - b > 0 := by
    have h8 : c ^ 2 = b ^ 2 - 4 := by
      nlinarith [h6]
    rw [h5]
    nlinarith [sq_nonneg (b - 1 / 2), sq_nonneg (c), sq_nonneg (a), sq_nonneg (d)]
  have h8 : c ≤ d := by
    nlinarith [h5, sq_nonneg (c - 1 / 2), sq_nonneg (a), sq_nonneg (b), sq_nonneg (d)]
  have h9 : a ≤ d := by
    rw [h4]
    nlinarith [h5, sq_nonneg (c), sq_nonneg (a), sq_nonneg (b), sq_nonneg (d)]
  have h10 : b ≤ d := by
    nlinarith [h7]
  have h11 : max c d = d := by 
    apply max_eq_right 
    linarith [h8]
  have h12 : max a b ≤ d := by
    cases' max_cases a b with h13 h13
    · -- case a ≥ b, max a b = a
      nlinarith [h9, h13]
    · -- case b > a, max a b = b
      nlinarith [h10, h13]
  have h13 : max (max a b) (max c d) = d := by 
    rw [h11]
    apply max_eq_right 
    linarith [h12]
  exact h13