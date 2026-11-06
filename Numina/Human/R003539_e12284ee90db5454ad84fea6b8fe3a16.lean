import Mathlib

theorem algebra_193239 :
  {D : ℕ | ∃ P Q : ℕ, 0 < P ∧ 0 < Q ∧ P + Q + P * Q = 90 ∧ D = P + Q} = {18} := by
  ext D
  simp
  constructor
  . -- Show that if there exists P and Q satisfying the equation, then D = 18.
    rintro ⟨P, hP, Q, hQ, h₀, hD⟩
    have h₂ : (P + 1) * (Q + 1) = 91 := by linarith
    have : P + Q = 18 := by
      have : P ≤ 90 := by nlinarith
      interval_cases P <;> omega
    rw [hD, this]
  . -- Check that D = 18 is indeed possible.
    intro hD
    use 6, by norm_num, 12
    norm_num [hD]