import Mathlib
/-Each term of a sequence, after the first term, is inversely proportional to the term preceding it, and the constant of proportionality stays the same. If the first term is 2 and the second term is 5, what is the 12th term?-/
theorem algebra_10237 {a : ℕ → ℝ} (ha : a 1 = 2) (ha' : a 2 = 5)
  (h : ∀ n, a (n + 1) * a n = a n * a (n - 1)) : a 12 = 5 := by
    -- Recall that two quantities are inversely proportional if their product is constant.  Therefore, the product of every pair of consecutive terms of the sequence is the same.  Since the first two terms are 2 and 5, the product of every pair of consecutive terms is 10.
    have hind : ∀ n, a (n + 1) * a n = 10 := by
      intro n
      induction' n with n ih
      · have := h 1
        simp [ha, ha'] at this ⊢
        linarith
      · have := h (n + 1)
        simp at this
        linarith
    -- auxiliary lemma : a n = 5 if n is even and a n = 2 if n is odd.
    have aux : ∀ n, (Even n → a n = 5) ∧ (Odd n → a n = 2) := by
      intro n
      induction' n with n ih
      · simp
        have := h 1
        simp [ha, ha'] at this
        linarith
      · rcases Nat.even_or_odd n with evenn | oddn
        · simp [evenn] at ih ⊢
          have := hind n
          simp [ih] at this
          linarith
        · simp [oddn] at ih ⊢
          have := hind n
          simp [ih] at this
          linarith
    -- Because 12 is even, by the above lemma, a 12 = 5.
    exact (aux 12).1 (Nat.even_iff.mpr rfl)
