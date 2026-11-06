import Mathlib

theorem other_26755 (k : ℕ) (hk : 0 < k) (A B : ℕ → ℕ)
    (hA1 : A 1 = k) (hA2 : A 2 = k)
    (hA : ∀ n, A (n + 2) = A n * A (n + 1))
    (hB1 : B 1 = 1) (hB2 : B 2 = k)
    (hB : ∀ n, B (n + 2) = (B (n + 1)^3 + 1) / B n) :
    ∀ n, 0 < n → ∃ m, A (2 * n) * B (n + 3) = m := by
  intro n hn
  refine ⟨A (2 * n) * B (n + 3), by simp⟩