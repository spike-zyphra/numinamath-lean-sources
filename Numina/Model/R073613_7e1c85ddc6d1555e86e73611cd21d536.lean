import Mathlib

theorem number_theory_289848 (A B : ℕ) (h₀ : A < 10) (h₁ : B < 10)
    (h₂ : IsSquare (15000 + 100 * A + 10 * B + 9)) :
    A + B = 3 := by
  rcases h₂ with ⟨k, hk⟩
  have h3 : k ^ 2 ≤ 15999 := by
    have h_max : 15000 + 100 * A + 10 * B + 9 ≤ 15999 := by
      have hA : A ≤ 9 := by linarith [h₀]
      have hB : B ≤ 9 := by linarith [h₁]
      omega
    linarith [hk, h_max]
  have h4 : k ≤ 126 := by
    nlinarith [show k ^ 2 ≤ 15999 by linarith [show k ^ 2 ≤ 15999 by linarith]]
  have h5 : k ≥ 123 := by
    by_contra h
    push_neg at h
    have : k ≤ 122 := by
      nlinarith
    have : k ^ 2 < 15000 := by
      nlinarith [show k ≤ 122 by nlinarith]
    have h_min : 15000 + 100 * A + 10 * B + 9 ≥ 15000 := by 
      omega
    nlinarith [hk]
  interval_cases k <;> omega