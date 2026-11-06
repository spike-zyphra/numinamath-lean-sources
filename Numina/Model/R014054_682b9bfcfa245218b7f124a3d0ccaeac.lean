import Mathlib

theorem number_theory_160206 (n : ℕ) :
    ∃ a b, a^2 + b^2 = 2^n * 1985 := by
  have h2 : ∀ (k : ℕ), ∃ a b, a^2 + b^2 = 2 ^ (2 * k) * 1985 := by
    intro k
    use (2 ^ k * 44), (2 ^ k * 7)
    ring_nf
  have h3 : ∀ (k : ℕ), ∃ a b, a^2 + b^2 = 2 ^ (2 * k + 1) * 1985 := by
    intro k
    use (2 ^ k * 51), (2 ^ k * 37)
    ring_nf
  cases' Nat.even_or_odd n with h h
  · -- If $n$ is even, let $n = 2k$ for some $k$.
    obtain ⟨k, hk⟩ := h
    rw [show n = 2 * k by linarith [hk]]
    have h4 : ∃ a b, a^2 + b^2 = 2 ^ (2 * k) * 1985 := h2 k
    exact h4
  · -- If $n$ is odd, let $n = 2k+1$ for some $k$.
    obtain ⟨k, hk⟩ := h
    rw [show n = 2 * k + 1 by linarith [hk]]
    have h5 : ∃ a b, a^2 + b^2 = 2 ^ (2 * k + 1) * 1985 := h3 k
    exact h5