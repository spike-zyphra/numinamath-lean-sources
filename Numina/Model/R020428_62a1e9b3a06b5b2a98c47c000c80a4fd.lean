import Mathlib


theorem algebra_150490 (a : ℕ → ℤ) (ha : ∀ n, 0 < a n)
    (h1 : a 1 = 1) (h2 : a 2 = 1) (h3 : a 3 = 1)
    (h4 : ∀ n, a n * a (n + 3) - a (n + 1) * a (n + 2) = 1) :
    ∀ n, ∃ k, a n + a (n + 2) = k * a (n + 1) := by
  intro n
  have h5 : a (n + 1) ∣ a n + a (n + 2) := by
    have eq2 : a (n + 1) ∣ a (n + 3) * (a n + a (n + 2)) := by
      have eq3 : a (n + 3) * (a n + a (n + 2)) = a (n + 1) * (a (n + 4) + a (n + 2)) := by
        have eq4 : a n * a (n + 3) - a (n + 1) * a (n + 2) = 1 := by
          specialize h4 n
          simpa using h4
        have eq5 : a (n + 1) * a (n + 4) - a (n + 2) * a (n + 3) = 1 := by
          specialize h4 (n + 1)
          simpa using h4
        linarith
      rw [eq3]
      exact dvd_mul_right _ _
    have eq3 : IsCoprime (a (n + 1)) (a (n + 3)) := by
      have eq8 : IsCoprime (a (n + 1)) (a (n + 3)) := by
        use (-a (n + 2))
        use (a n)
        have eq9 : a (n + 1) * (-a (n + 2)) + a (n + 3) * (a n) = 1 := by
          have eq10 : a n * a (n + 3) - a (n + 1) * a (n + 2) = 1 := by
            specialize h4 n
            simpa using h4
          linarith
        linarith
      exact eq8
    -- Since `gcd a_{n+1} a_{n+3} = 1` and `a_{n+1}` divides `a_{n+3} \cdot (a_n + a_{n+2})`, then `a_{n+1}` divides `a_n + a_{n+2}`.
    apply IsCoprime.dvd_of_dvd_mul_left eq3 eq2
  rcases h5 with ⟨k, hk⟩
  refine' ⟨k, by linarith⟩