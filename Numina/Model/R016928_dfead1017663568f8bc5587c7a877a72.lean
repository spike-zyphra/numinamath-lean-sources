import Mathlib

theorem number_theory_102668 (a b c : ℕ) (h₀ : a < b) (h₁ : a < c) (h₂ : b < c)
    (h₃ : |(a * b : ℤ) - (a * c : ℤ)| = 1) (h₄ : |(a * b : ℤ) - (b * c : ℤ)| = 49) :
    a + b + c = 16 := by

  have h31 : (a * b : ℤ) - (a * c : ℤ) = 1 ∨ (a * b : ℤ) - (a * c : ℤ) = -1 := by
    cases' eq_or_eq_neg_of_abs_eq h₃ with h32 h32
    · 
      left
      linarith
    · 
      right
      linarith

  have h32 : (a * b : ℤ) - (b * c : ℤ) = 49 ∨ (a * b : ℤ) - (b * c : ℤ) = -49 := by
    cases' eq_or_eq_neg_of_abs_eq h₄ with h33 h33
    · 
      left
      linarith
    · 
      right
      linarith

  have h5 : (a * b : ℤ) - (a * c : ℤ) = -1 := by
    cases h31 with
    | inl h311 =>
      exfalso
      nlinarith [show (b : ℤ) < (c : ℤ) by omega]
    | inr h312 =>
      linarith

  have h6 : (a : ℤ) = 1 := by
    have h7 : (a : ℤ) * ((b : ℤ) - (c : ℤ)) = -1 := by
      linarith [h5]
    have h8 : (b : ℤ) < (c : ℤ) := by
      omega
    have h9 : (a : ℤ) > 0 := by
      nlinarith [sq_nonneg ((a : ℤ) : ℤ), sq_nonneg (( (b : ℤ) - (c : ℤ) ) : ℤ)]
    have h9b : (a : ℤ) > 0 := by
      nlinarith [sq_nonneg ((a : ℤ) : ℤ), sq_nonneg (( (b : ℤ) - (c : ℤ) ) : ℤ)]
    have h9c : ((b : ℤ) - (c : ℤ)) < 0 := by
      omega
    have h11 : (a : ℤ) = 1 := by
      have h13 : (a : ℤ) * ((b : ℤ) - (c : ℤ)) = -1 := h7
      have h14 : (a : ℤ) = 1 := by
        nlinarith [show (a : ℤ) > 0 by tauto, sq_nonneg ((a : ℤ) * ((b : ℤ) - (c : ℤ))), sq_nonneg ((b : ℤ) - (c : ℤ)), sq_pos_of_neg (show ((b : ℤ) - (c : ℤ)) < 0 by omega)]
      linarith
    linarith

  -- Prove a = 1
  have ha1 : a = 1 := by
    omega

  -- Prove c - b = 1
  have h7' : (c : ℤ) - (b : ℤ) = 1 := by
    have h5' : (a * b : ℤ) - (a * c : ℤ) = -1 := h5
    rw [show (a : ℤ) = 1 by omega] at h5'
    nlinarith

  cases h32 with
  | inl h321 =>
    rw [show (a : ℤ) = 1 by omega] at h321
    have h81 : (b : ℤ) = 7 := by
      nlinarith [show (c : ℤ) - (b : ℤ) = 1 by omega, sq_nonneg ((b : ℤ) : ℤ), sq_nonneg ((c : ℤ) - (b : ℤ))]
    have h82 : (c : ℤ) = 8 := by
      nlinarith [show (c : ℤ) - (b : ℤ) = 1 by omega, h81]
    have h91 : b = 7 := by
      omega
    have h92 : c = 8 := by
      omega
    omega
  | inr h322 =>
    rw [show (a : ℤ) = 1 by omega] at h322
    have h81 : (b : ℤ) = 7 := by
      nlinarith [show (c : ℤ) - (b : ℤ) = 1 by omega, sq_nonneg ((b : ℤ) : ℤ), sq_nonneg ((c : ℤ) - (b : ℤ))]
    have h82 : (c : ℤ) = 8 := by
      nlinarith [show (c : ℤ) - (b : ℤ) = 1 by omega, h81]
    have h91 : b = 7 := by
      omega
    have h92 : c = 8 := by
      omega
    omega