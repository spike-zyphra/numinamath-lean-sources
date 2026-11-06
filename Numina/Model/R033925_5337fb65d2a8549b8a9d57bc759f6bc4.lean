import Mathlib

def a : ℕ → ℕ
| 0 => 1
| 1 => 3
| n + 2 => a (n + 1) + a n

theorem number_theory_2704 : {n | n ∈ Finset.range 100 ∧ 5 ∣ a n}.encard = 0 := by
  have h1 : ∀ n : ℕ, n < 100 → ¬ (5 ∣ a n) := by
    intro n hn
    interval_cases n <;> norm_num [a] <;> omega
  have h2 : {n | n ∈ Finset.range 100 ∧ 5 ∣ a n} = ∅ := by
    ext n
    simp only [Finset.mem_range, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    rcases h with ⟨hn1, h5⟩
    have h3 : n < 100 := by
      omega
    -- From h1, since n < 100, then ¬ 5 ∣ a n
    have h4 : ¬ (5 ∣ a n) := h1 n h3
    tauto 
  rw [h2]
  simp