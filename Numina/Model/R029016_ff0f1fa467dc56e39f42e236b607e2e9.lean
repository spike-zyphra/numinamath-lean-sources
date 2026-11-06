import Mathlib

theorem algebra_21638 (a b c : ℕ) (h₀ : a^2 + b^2 = c^2) (h₁ : a = 9)
    (h₂ : ∃ n, b = n ∧ c = n + 1) :
    a + b + c = 90 := by
  rcases h₂ with ⟨n, h₃, h₄⟩
  rw [h₁] at h₀
  rw [h₃] at h₀
  rw [h₄] at h₀
  have eqn2 : n = 40 := by
    nlinarith
  have h₆ : b = 40 := by
    linarith [h₃, eqn2]
  have h₇ : c = 41 := by
    omega
  calc
    a + b + c = 9 + 40 + 41 := by rw [h₁, h₆, h₇]
    _ = 90 := by norm_num