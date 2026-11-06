import Mathlib

theorem number_theory_15494 (S E A B : ℕ) (h₀ : S ≠ E) (h₁ : S ≠ A) (h₂ : S ≠ B)
    (h₃ : E ≠ A) (h₄ : E ≠ B) (h₅ : A ≠ B) (h₆ : Nat.digits 10 (S * 100 + E * 10 + A) =
    [1, 7, 8]) (h₇ : Nat.digits 10 (E * 100 + B * 10 + S) = [8, 7, 1]) :
    S * 100 + E * 10 + A = 871 := by
  have h8 : S * 100 + E * 10 + A = 871 := by
    have h9 : Nat.digits 10 (S * 100 + E * 10 + A) = [1, 7, 8] := h₆
    have h10 : (S * 100 + E * 10 + A) = 871 := by
      rw [← Nat.ofDigits_digits 10 (S * 100 + E * 10 + A)]
      rw [h9]
      norm_num [Nat.ofDigits]
      all_goals omega
    exact h10
  exact h8