import Mathlib

theorem number_theory_16756 : ∑ d in (6 : ℕ).divisors, (1 : ℚ) / d = 2 := by
  have h1 : (6 : ℕ).divisors = {1, 2, 3, 6} := by
    rfl
  rw [h1]
  norm_num [Finset.sum_insert, Finset.sum_singleton]
  all_goals try { native_decide }
  <;> try { tauto }
  all_goals try { ring }
  <;> try { omega }
  <;> try { native_decide }
  all_goals try { norm_num }
  all_goals try { native_decide }
  all_goals try { ring }