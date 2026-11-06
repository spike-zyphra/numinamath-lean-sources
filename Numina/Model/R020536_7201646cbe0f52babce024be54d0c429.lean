import Mathlib

theorem algebra_152119 (k : ℤ) (h : ∃ a d, a^2 = 36 + k ∧ (a + d)^2 = 300 + k ∧ (a + 2 * d)^2 = 596 + k) :
    k = 925 := by 
  rcases h with ⟨a, d, h1, h2, h3⟩
  have eq1 : 2 * a * d + d ^ 2 = 264 := by
    nlinarith
  have eq2 : 2 * a * d + 3 * d ^ 2 = 296 := by
    nlinarith
  have h4 : 2 * d ^ 2 = 32 := by
    nlinarith
  have h5 : d ^ 2 = 16 := by
    linarith
  have h6 : d = 4 ∨ d = -4 := by
    have h7 : d ^ 2 - 16 = 0 := by linarith 
    have h8 : (d - 4) * (d + 4) = 0 := by 
      nlinarith
    cases (mul_eq_zero.mp h8) with 
    | inl h9 => 
      left
      linarith
    | inr h10 => 
      right
      linarith
  cases h6 with
  | inl h7 =>
    have ha1 : a = 31 := by
      rw [h7] at eq2
      nlinarith
    rw [ha1] at h1
    nlinarith
  | inr h7 =>
    have ha1 : a = -31 := by
      rw [h7] at eq2
      nlinarith
    rw [ha1] at h1
    nlinarith