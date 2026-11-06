import Mathlib

theorem number_theory_316436 (m n : ℕ) (hm : m.Prime) (hn : n.Prime)
    (h : 5 * m + 7 * n = 129) : m + n = 19 ∨ m + n = 25 := by
  have h1 : m ≤ 25 := by
    omega
  have h2 : n ≤ 18 := by
    omega
  interval_cases m <;> interval_cases n <;> norm_num at h hm hn ⊢ <;> try { tauto }