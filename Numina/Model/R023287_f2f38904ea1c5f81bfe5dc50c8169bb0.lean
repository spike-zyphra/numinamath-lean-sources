import Mathlib

theorem algebra_323201 {m n : ℕ} (hm : Odd m) (hn : Odd n)
    (h : ∃ p q, p.Prime ∧ q.Prime ∧ p^2 + 4 * m * p - 3 * n * p + 4 * m^2 + n^2 + 9 = 0 ∧
      q^2 + 4 * m * q - 3 * n * q + 4 * m^2 + n^2 + 9 = 0) :
    p = 2 ∧ q = 11 := by
  rcases h with ⟨p, q, hp, hq, he1, he2⟩
  all_goals
    omega