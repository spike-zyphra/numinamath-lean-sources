import Mathlib

theorem number_theory_317227 {a b : ℕ → ℝ}
    (ha : ∀ n, a n = (2 + Real.sqrt 7) ^ (2 * n + 1))
    (hb : ∀ n, b n = a n - ⌊a n⌋) :
    ∀ n > 0, Odd (a n * b n) := by

  intro n hn

  have eq2 : ∃ k : ℝ, a n * b n = 2 * k + 1 := by
    use ( (a n * b n - 1 ) / 2 )
    linarith

  rcases eq2 with ⟨k, hk⟩

  exact ⟨k, by linarith [hk]⟩