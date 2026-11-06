import Mathlib

theorem algebra_152379 (a b c d e f : ℕ) (h₀ : c = a * b) (h₁ : d = b * c)
    (h₂ : e = c * d) (h₃ : f = d * e) (h₄ : e = 108) :
    a * b * c * d * e * f = 136048896 := by
  have h5 : c * d = 108 := by
    calc
      c * d = e := by rw [h₂]
      _ = 108 := by rw [h₄]
  -- Express d in terms of a and b.
  have h6 : c = a * b := by
    linarith
  have h7 : d = b * c := by
    linarith
  have h8 : d = a * b ^ 2 := by
    rw [h7, h6]
    ring
  -- Substitute into the equation c * d = 108 to get a^2 * b^3 = 108.
  have h9 : a ^ 2 * b ^ 3 = 108 := by
    have h10 : c * d = 108 := h5
    rw [h6, h8] at h10
    nlinarith
  have h10 : a ≤ 10 := by
    have h12 : a ^ 2 ∣ 108 := by
      use b ^ 3
      all_goals nlinarith
    have h13 : a ≤ 10 := by
      by_contra h14
      push_neg at h14
      have h15 : a > 10 := by linarith
      have h16 : a ^ 2 > 100 := by
        nlinarith [sq_nonneg (a - 10 : ℕ)]
      have h17 : a ^ 2 ∣ 108 := h12
      have h18 : a ^ 2 ≤ 108 := by
        exact Nat.le_of_dvd (by norm_num) h17
      nlinarith
    linarith
  have h11 : b ≤ 22 := by
    have h12 : b ^ 3 ∣ 108 := by
      use a ^ 2
      all_goals nlinarith
    have h13 : b ≤ 22 := by
      by_contra h14
      push_neg at h14
      have h15 : b > 22 := by linarith
      have h16 : b ^ 3 > 108 := by
        have h17 : b > 22 := by linarith
        have h18 : b ^ 3 > 22 ^ 3 := by
          apply Nat.pow_lt_pow_left 
          all_goals linarith
        nlinarith
      have h14 : b ^ 3 ∣ 108 := h12
      have h14 : b ^ 3 ≤ 108 := by
        exact Nat.le_of_dvd (by norm_num) h12
      nlinarith
    linarith
  interval_cases a <;> interval_cases b
    <;> norm_num [h₃, h₄, h₂, h₀, h₁, h5, h6, h7, h8, h9] at *
    <;> omega