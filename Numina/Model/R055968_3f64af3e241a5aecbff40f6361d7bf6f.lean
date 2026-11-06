import Mathlib

theorem algebra_120834 {a b c d : ℤ} (h : a < b ∧ b < c ∧ c < d) :
    (a + b) * (c + d) < (a + c) * (b + d) ∧ (a + c) * (b + d) < (a + d) * (b + c) := by
  rcases h with ⟨h1, h2, h3⟩
  constructor
  · -- Prove the first inequality (a + b) * (c + d) < (a + c) * (b + d)
    nlinarith [h1, h2, h3, mul_pos (show 0 < b - a by linarith) (show 0 < c - b by linarith), mul_pos (show 0 < c - b by linarith) (show 0 < d - c by linarith)]
  · -- Prove the second inequality (a + c) * (b + d) < (a + d) * (b + c)
    nlinarith [h1, h2, h3, mul_pos (show 0 < b - a by linarith) (show 0 < c - b by linarith), mul_pos (show 0 < c - b by linarith) (show 0 < d - c by linarith)]