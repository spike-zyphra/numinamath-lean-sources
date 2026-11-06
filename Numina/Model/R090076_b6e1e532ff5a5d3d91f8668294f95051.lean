import Mathlib

theorem number_theory_79190 (a b c d p q : ℤ) (_ : 0 < a) (h₀ : 0 < b) (h₁ : 0 < c) (h₂ : 0 < d)
    (h₃ : 0 < p) (h₄ : 0 < q) (h₅ : a * d - b * c = 1) (h₆ : (a / b : ℚ) > (p / q : ℚ))
    (h₇ : (p / q : ℚ) > (c / d : ℚ)) :
    q ≥ b + d ∧ (q = b + d → p = a + c) := by 
  have ha1 : a * q > b * p := by
    have h6' : (a / b : ℚ) > (p / q : ℚ) := h₆
    have h8 : (a : ℚ) * (q : ℚ) > (b : ℚ) * (p : ℚ) := by
      have h9 : (b : ℚ) > 0 := by exact_mod_cast h₀
      have h10 : (q : ℚ) > 0 := by exact_mod_cast h₄
      apply (div_lt_div_iff (by positivity) (by positivity)).1 at h6'
      linarith
    norm_cast at h8 ⊢
    all_goals linarith
  have ha2 : p * d > c * q := by
    have h7' : (p / q : ℚ) > (c / d : ℚ) := h₇
    have h8 : (p : ℚ) * (d : ℚ) > (c : ℚ) * (q : ℚ) := by
      have h9 : (q : ℚ) > 0 := by exact_mod_cast h₄
      have h10 : (d : ℚ) > 0 := by exact_mod_cast h₂
      apply (div_lt_div_iff (by positivity) (by positivity)).1 at h7'
      linarith
    norm_cast at h8 ⊢
    all_goals linarith
  have h8 : q ≥ b + d := by
    nlinarith [sq_nonneg (q - b), sq_nonneg (q - d), sq_nonneg (a * q - b * p), sq_nonneg (p * d - c * q), h₅]
  have h9 : q ≥ b + d := h8
  have h10 : q = b + d → p = a + c := by
    intro h
    have j₁ : p * d > c * q := ha2
    have j₂ : a * q > b * p := ha1
    have h4 : p * d > c * (b + d) := by
      rw [show q = b + d by linarith] at j₁
      linarith
    have h3 : a * (b + d) > b * p := by
      rw [show q = b + d by linarith] at j₂
      linarith
    nlinarith [sq_nonneg (p - (a + c)), sq_nonneg (a * d - b * c - 1), sq_nonneg (q - (b + d)), h₀, h₁, h₂, h₃, h₄, h₅]
  constructor
  · exact h8
  · exact h10