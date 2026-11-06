import Mathlib

/- Given that $a$, $b$, and $c$ are distinct integers, the minimum value of $4\left( {{a}^{2}}+{{b}^{2}}+{{c}^{2}} \right)-{{\left( a+b+c \right)}^{2}}$ is ___          ___. -/
theorem algebra_12245 (a b c : ℤ) (h₀ : a ≠ b) (h₁ : a ≠ c) (h₂ : b ≠ c) :
    4 * (a ^ 2 + b ^ 2 + c ^ 2) - (a + b + c) ^ 2 ≥ 8 := by
  have h3 : (a - b) ^ 2 ≥ 1 := by
    have h4 : a - b ≠ 0 := by
      intro h
      apply h₀
      linarith
    have h5 : (a - b) ^ 2 ≥ 1 := by
      have h6 : (a - b : ℤ) ≠ 0 := by
        intro h
        apply h₀
        linarith
      have h7 : (a - b : ℤ) ^ 2 ≥ 1 := by
        have h8 : (a - b : ℤ) < 0 ∨ (a - b : ℤ) > 0 := by
          by_contra h
          push_neg at h
          have h9 : (a - b : ℤ) = 0 := by nlinarith
          tauto
        rcases h8 with (h8 | h8)
        · nlinarith [sq_nonneg (a - b)]
        · nlinarith [sq_nonneg (a - b)]
      nlinarith
    linarith
  have h4 : (a - c) ^ 2 ≥ 1 := by
    have h4 : a - c ≠ 0 := by
      intro h
      apply h₁
      linarith
    have h5 : (a - c) ^ 2 ≥ 1 := by
      have h6 : (a - c) ≠ 0 := by
        intro h
        apply h₁
        linarith
      have h7 : (a - c : ℤ) ^ 2 ≥ 1 := by
        have h8 : (a - c : ℤ) < 0 ∨ (a - c : ℤ) > 0 := by
          by_contra h
          push_neg at h
          have h9 : (a - c : ℤ) = 0 := by nlinarith
          tauto
        rcases h8 with (h8 | h8)
        · nlinarith [sq_nonneg (a - c)]
        · nlinarith [sq_nonneg (a - c)]
      nlinarith
    linarith
  have h5 : (b - c) ^ 2 ≥ 1 := by
    have h6 : b - c ≠ 0 := by
      intro h
      apply h₂
      linarith
    have h7 : (b - c) ^ 2 ≥ 1 := by
      have h8 : (b - c) ≠ 0 := by
        intro h
        apply h₂
        linarith
      have h9 : (b - c : ℤ) ^ 2 ≥ 1 := by
        have h10 : (b - c : ℤ) < 0 ∨ (b - c : ℤ) > 0 := by
          by_contra h
          push_neg at h
          have h11 : (b - c : ℤ) = 0 := by nlinarith
          tauto
        rcases h10 with (h10 | h10)
        · nlinarith [sq_nonneg (b - c)]
        · nlinarith [sq_nonneg (b - c)]
      nlinarith
    linarith
  nlinarith [sq_nonneg (a - b - 1), sq_nonneg (a - c - 1), sq_nonneg (b - c - 1),
            sq_pos_of_ne_zero (show (a - b : ℤ) ≠ 0 by intro h; apply h₀; linarith),
            sq_pos_of_ne_zero (show (a - c : ℤ) ≠ 0 by intro h; apply h₁; linarith),
            sq_pos_of_ne_zero (show (b - c : ℤ) ≠ 0 by intro h; apply h₂; linarith),
            sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]