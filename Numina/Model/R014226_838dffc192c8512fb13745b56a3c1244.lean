import Mathlib

open Finset

theorem number_theory_105489 {A : ℕ → Set ℕ}
    (hA : ∀ n, A n = {x | 2 ^ n < x ∧ x ≤ 2 ^ (n + 1)}) :
    (A 2014).ncard = 2 ^ 2014 ∧
    ∃ n, (A n).ncard = 128 := by
  have h1 : ∀ n, (A n).ncard = 2 ^ n := by
    intro n
    have h2 : A n = Set.Ioc (2 ^ n) (2 ^ (n + 1)) := by
      ext x
      simp [hA]
      <;> try omega
    rw [h2]
    rw [Set.ncard_eq_toFinset_card']
    simp
    <;> try ring_nf <;> try omega
  constructor
  · -- First part: proving (A 2014).ncard = 2 ^ 2014
    have h3 : (A 2014).ncard = 2 ^ 2014 := by
      specialize h1 2014
      simpa using h1
    exact h3
  · -- Second part: proving ∃ n, (A n).ncard = 128
    use 7
    have h4 : (A 7).ncard = 128 := by
      have h5 : (A 7).ncard = 2 ^ 7 := h1 7
      norm_num at h5 ⊢
      all_goals linarith
    exact h4