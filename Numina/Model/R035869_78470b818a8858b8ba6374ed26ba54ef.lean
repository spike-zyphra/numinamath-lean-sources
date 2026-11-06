import Mathlib

theorem number_theory_290741 (a : ℕ → ℤ) (h₀ : a 1 = 1)
    (h₁ : ∀ n ≥ 1, a (n + 1) = a n ^ 2 + a n + 1) :
    ∀ n ≥ 1, (a n) ^ 2 + 1 ∣ (a (n + 1)) ^ 2 + 1 := by
        intro n hn
        have h2 : a (n + 1) = a n ^ 2 + a n + 1 := h₁ n hn
        rw [h2]
        use (a n ^ 2 + 2 * a n + 2)
        ring_nf
        <;> nlinarith [sq_nonneg (a n), sq_nonneg (a n + 1), sq_nonneg (a n - 1)]