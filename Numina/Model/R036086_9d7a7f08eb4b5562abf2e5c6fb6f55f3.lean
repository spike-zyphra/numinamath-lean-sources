import Mathlib

theorem number_theory_261448 {a b c : ℤ} (h : a^2 + b^2 = c) (n : ℕ) (hn : n > 0) :
    ∃ d e, c^n = d^2 + e^2 := by
  have h1 : ∀ (n : ℕ), n > 0 → ∃ d e, c ^ n = d ^ 2 + e ^ 2 := by
    intro n hn
    induction n with
    | zero =>
      linarith
    | succ n ih =>
      cases n with
      | zero =>
        -- Base case n = 1
        use a, b
        rw [show c = a ^ 2 + b ^ 2 by linarith]
        all_goals norm_num
      | succ n =>
        rcases ih (by linarith) with ⟨d, e, h2⟩
        use (a * d - b * e), (a * e + b * d)
        rw [pow_succ, h2]
        rw [show c = a ^ 2 + b ^ 2 by linarith]
        ring_nf
  specialize h1 n hn
  simpa using h1