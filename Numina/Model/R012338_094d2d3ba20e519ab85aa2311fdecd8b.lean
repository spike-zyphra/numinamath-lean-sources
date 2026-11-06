import Mathlib

theorem number_theory_248104 (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (a : ℕ → ℕ)
    (ha1 : a 1 = p) (ha2 : a 2 = q)
    (han : ∀ n > 0, ∃ m > 0, a n + a (n + 1) = 2 ^ m → a (n + 2) = 2)
    (han' : ∀ n > 0, ¬∃ m > 0, a n + a (n + 1) = 2 ^ m →
      a (n + 2) = sInf {x | Odd x ∧ Prime x ∧ x ∣ a n + a (n + 1)}) :
    ∃ k > 0, a k = 2 := by
  have h2 := han' 1 (by norm_num)
  have h3 : ∃ m > 0, a 1 + a (1 + 1) = 2 ^ m → a (1 + 2) = sInf {x | Odd x ∧ Prime x ∧ x ∣ a 1 + a (1 + 1)} := by
    use 1
    constructor
    · norm_num
    · -- Show that the implication is true.
      simp only [ha1, ha2] at *
      have h3ne : p + q ≠ 2 := by
        by_contra h_eq
        -- Assume p + q = 2
        have h4 : p = 0 ∨ q = 0 := by
          omega
        rcases h4 with (hp0 | hq0)
        · -- Case p = 0
          have h5 : ¬ (p).Prime := by
            rw [hp0]
            norm_num
          contradiction
        · -- Case q = 0
          have h6 : ¬ (q).Prime := by
            rw [hq0]
            norm_num
          contradiction
      simp [show p + q ≠ 2 by exact_mod_cast h3ne]
  contradiction