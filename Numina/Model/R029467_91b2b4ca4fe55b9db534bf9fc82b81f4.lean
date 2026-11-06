import Mathlib

theorem number_theory_13132 {A B C : ℕ} (h₀ : A ≠ 0) (h₁ : B ≠ 0) (h₂ : C ≠ 0)
    (h₃ : A ≠ B) (h₄ : A ≠ C) (h₅ : B ≠ C) (h₆ : A < 6) (h₇ : B < 6) (h₈ : C < 6)
    (h₉ : Nat.ofDigits 6 [B, A] + Nat.ofDigits 6 [C] = Nat.ofDigits 6 [0, C])
    (h₁₀ : Nat.ofDigits 6 [B, A] + Nat.ofDigits 6 [A, B] = Nat.ofDigits 6 [C, C]) :
    Nat.ofDigits 10 [C, B, A] = 415 := by

  simp [Nat.ofDigits, List.foldl] at h₉ h₁₀ ⊢
  have h1 : 6 * A + B = 5 * C := by
    omega
  have h2 : A + B = C := by
    omega

  have h3 : A = 4 * B := by
    omega

  have h4 : C = 5 * B := by
    omega

  have h5 : B = 1 := by
    omega

  have h6 : A = 4 := by
    omega

  have h7 : C = 5 := by
    omega

  simp [Nat.ofDigits, List.foldl, h5, h6, h7]
  all_goals omega