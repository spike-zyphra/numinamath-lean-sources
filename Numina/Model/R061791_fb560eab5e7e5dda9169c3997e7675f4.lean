import Mathlib

theorem algebra_211892 {A B C : ℤ} (h₀ : A + B + C = 0) :
    IsSquare (2 * (A ^ 4 + B ^ 4 + C ^ 4)) := by
  have h1 : C = -A - B := by linarith
  rw [h1]
  -- Prove equality of the given expression to a square.
  have h2 : 2 * (A ^ 4 + B ^ 4 + (-A - B) ^ 4) = (2 * (A ^ 2 + A * B + B ^ 2)) ^ 2 := by
    ring_nf
  -- Then it's square.
  rw [h2]
  exact ⟨2 * (A ^ 2 + A * B + B ^ 2), by ring⟩