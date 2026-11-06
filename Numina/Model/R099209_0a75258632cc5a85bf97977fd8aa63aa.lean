import Mathlib

theorem algebra_239542 {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hroots : ∃ m n, m ≠ n ∧ m^2 + a * m + b + 1 = 0 ∧ n^2 + a * n + b + 1 = 0) :
    ¬Prime (a^2 + b^2) := by 
  rcases hroots with ⟨m, n, hmn, hm, hn⟩
  have h1 : m ^ 2 + a * m + b + 1 > 0 := by 
    omega
  linarith