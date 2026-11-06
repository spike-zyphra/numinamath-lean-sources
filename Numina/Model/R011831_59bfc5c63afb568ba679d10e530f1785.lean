import Mathlib

theorem algebra_52546 (k : ℤ) (h : ∃ a d, a^2 = 36 + k ∧ (a+d)^2 = 300 + k ∧ (a+2*d)^2 = 596 + k) :
    k = 925 := by
  rcases h with ⟨a, d, h1, h2, h3⟩
  have eq1 : 2 * a * d + d ^ 2 = 264 := by
    nlinarith
  have eq2 : 4 * a * d + 4 * d ^ 2 = 560 := by
    nlinarith
  have h7 : d ^ 2 = 16 := by
    nlinarith [sq_nonneg (d : ℤ), sq_nonneg (a : ℤ)]
  have h8 : d = 4 ∨ d = -4 := by
    have h9 : d ^ 2 - 16 = 0 := by
      linarith
    have h10 : (d - 4) * (d + 4) = 0 := by
      nlinarith
    cases mul_eq_zero.mp h10 with
    | inl h11 => 
      left
      omega
    | inr h12 => 
      right
      omega
  have h10 : a * d = 124 := by
    have h11 : 2 * a * d = 248 := by
      nlinarith [h7]
    nlinarith
  cases h8 with
  | inl h11 => 
    have h13 : a = 31 := by
      rw [h11] at h10
      nlinarith
    rw [h13] at h1
    nlinarith
  | inr h12 => 
    have h14 : a = -31 := by
      rw [h12] at h10
      nlinarith
    rw [h14] at h1
    nlinarith