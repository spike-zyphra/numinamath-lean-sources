import Mathlib

theorem number_theory_82056 :
    ¬∃ a b : ℤ, 0 < a ∧ 0 < b ∧ 4 * a * (a + 1) = b * (b + 3) := by
  rintro ⟨a, b, ha, hb, heq⟩
  have h1 : b ≤ 2 * a + 1 := by
    nlinarith [sq_nonneg (b - 2 * a - 1), sq_nonneg (b + 3 - 2 * a), sq_nonneg (a - 0), sq_nonneg (b - 0)]
  have h2 : b ≥ 2 * a := by
    nlinarith [sq_nonneg (b - 2 * a), sq_nonneg (b + 3 - 2 * (a + 1)), sq_nonneg (a - 0), sq_nonneg (b - 0)]
  have h3 : b = 2 * a ∨ b = 2 * a + 1 := by 
    omega
  rcases h3 with h4 | h5
  · -- Assume b = 2 * a
    rw [h4] at heq
    nlinarith
  · -- Assume b = 2 * a + 1
    rw [h5] at heq
    nlinarith