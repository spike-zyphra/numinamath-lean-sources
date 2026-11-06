import Mathlib

theorem number_theory_120879 :
    IsLeast {n | ∃ k, n = ∑ i ∈ Finset.range 10, (k + i) ∧ n % 37 = 0 ∧ k ≥ 1000} 10175 := by
  constructor
  · -- Show that 10175 is in the set
    use 1013
    native_decide
  · -- We need to prove that if n is in the set, then n >= 10175
    intro n hn
    rcases hn with ⟨k, hk_eq, hk_mod, hk_k⟩
    have h1 : n = 10 * k + 45 := by
      rw [hk_eq]
      norm_num [Finset.sum_range_succ]
      <;> omega 
    rw [h1] at hk_mod 
    omega 
    <;> try { contradiction }
    <;> tauto 
    <;> try { native_decide }