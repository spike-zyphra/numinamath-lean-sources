import Mathlib

theorem number_theory_137157 (f : ℕ → ℕ)
    (h₀ : StrictMono f)
    (h₁ : ∀ m n, Nat.Coprime m n → f (m * n) = f m * f n)
    (h₂ : f 2 = 2)
    (h₃ : ∀ n, 0 < f n) :
    ∀ n, f n = n := by

  have h4 : f 0 < f 1 := by
    apply h₀
    all_goals norm_num

  have h5 : 0 < f 0 := by
    apply h₃ 0

  have h6 : 0 < f 1 := by
    apply h₃ 1

  have h7 : f 1 < f 2 := by
    apply h₀
    all_goals norm_num

  have h8 : f 1 < 2 := by
    have h7' : f 1 < f 2 := by
      apply h₀
      all_goals norm_num
    have h₂' : f 2 = 2 := h₂
    linarith

  have h9 : f 1 = 1 := by
    have h8' : f 1 < 2 := h8
    have h6' : 0 < f 1 := h6
    have h10 : f 1 = 1 := by
      omega
    exact h10

  have h10 : f 0 < 1 := by
    have h4' : f 0 < f 1 := h4
    have h9' : f 1 = 1 := h9
    linarith

  have h11 : 0 < f 0 := h5

  linarith