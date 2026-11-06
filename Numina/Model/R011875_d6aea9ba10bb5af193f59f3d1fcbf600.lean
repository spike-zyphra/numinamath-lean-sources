import Mathlib

theorem number_theory_155240 :
    {n : ℕ | ∃ a b, n = 10 * a + b ∧ a ≠ 0 ∧ a < 10 ∧ b < 10 ∧ a ^ 3 + b ^ 3 = n + 3} = {32} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First direction: if n is in the set, then n = 32
    rintro ⟨a, b, hn, ha1, ha2, hb1, h⟩
    have h1 : a ≤ 9 := by linarith
    have h2 : b ≤ 9 := by linarith
    interval_cases a <;> interval_cases b <;> omega
  · -- Second direction: n = 32 implies n is in the set
    intro h
    rw [h]
    use 3, 2
    all_goals norm_num