import Mathlib

lemma l_sum_2pow (k : ℕ) : ∑ i ∈ Finset.range (k + 1), 2 ^ i = 2 ^ (k + 1) - 1 := by
    induction k with
    | zero => simp
    | succ k ik =>
      rw [Finset.range_succ, Finset.sum_insert]
      rw [ik]
      rw [(Nat.add_sub_assoc Nat.one_le_two_pow (2 ^ (k + 1))).symm]
      rw [Nat.two_pow_succ (k + 1)]
      exact Finset.not_mem_range_self

abbrev is_super_increasing1 (seq : ℕ → ℕ) : Prop :=
  ∀ i, seq i > (∑ j ∈ Finset.range i, seq j)

theorem number_theory_4970
    (a : ℕ → ℕ)
    (h_asi : is_super_increasing1 a)
    : ∀ j, (a j ≥ 2 ^ j) := by 
  intro j
  induction' j using Nat.strongRecOn with j ih
  
  cases j with
  | zero => 
    specialize h_asi 0
    simp [Finset.sum_range_zero] at h_asi
    all_goals omega
  | succ j => 
    have h1 : a (j + 1) > ∑ i ∈ Finset.range (j + 1), a i := by
      specialize h_asi (j + 1)
      simpa using h_asi
    have h2 : ∑ i ∈ Finset.range (j + 1), a i ≥ ∑ i ∈ Finset.range (j + 1), (2 ^ i) := by
      apply Finset.sum_le_sum
      intro i hi
      have h3 : i < j + 1 := by
        simp at hi ⊢ 
        omega 
      have h4 : a i ≥ 2 ^ i := by 
        apply ih i 
        all_goals omega 
      linarith
    have h3 : ∑ i ∈ Finset.range (j + 1), (2 ^ i) = 2 ^ (j + 1) - 1 := by 
      apply l_sum_2pow 
    -- From h3 and h2 we get $∑_{i \in range (j + 1)} (a i) \geq 2^ (j + 1) - 1$
    -- From h1 we have $a (j + 1) > \sum_{i \in range (j + 1)} (a i)$
    -- Therefore $a (j + 1) > 2 ^ (j + 1) - 1$, which means $a (j + 1) \geq 2 ^ (j + 1)$
    have h4 : ∑ i ∈ Finset.range (j + 1), a i ≥ (2 ^ (j + 1) - 1) := by 
      linarith [h3, h2]
    have h10 : a (j + 1) ≥ 2 ^ (j + 1) := by 
      omega 
    exact_mod_cast h10