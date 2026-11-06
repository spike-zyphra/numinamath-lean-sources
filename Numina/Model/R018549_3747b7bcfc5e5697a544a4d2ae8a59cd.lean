import Mathlib

theorem number_theory_239803 (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (h : ∀ n ≥ 2, a (n + 1) = sInf {p | p.Prime ∧ p ∣ a (n - 1) + a n}) :
    ∃ q : ℚ, q = ∑' n, a n / 10 ^ (n + 1) := by
  let q := ∑' n : ℕ, (a n) / 10 ^ (n + 1)
  use q
  all_goals try { rfl }
  <;> try { simp_all [q] }
  <;> try { linarith }
  <;> try { 
    simp [tsum_eq_zero_of_eventually_zero]
    <;> norm_num 
  }