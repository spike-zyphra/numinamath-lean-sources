import Mathlib

theorem number_theory_289338 :
    IsLeast {k | 2019 < k ∧ 9 ∣ ∑ i ∈ Finset.Icc 1 k, i * 10 ^ (i - 1)} 2024 := by
  constructor
  · -- Show 2024 is in the set
    constructor
    · -- Show 2024 > 2019
      norm_num
    · -- Show that 9 divides the sum from 1 to 2024
      native_decide
  · -- Show there is no smaller element in the set.
    intro k hk
    rcases hk with ⟨hk1, hk2⟩
    by_contra h
    push_neg at h
    have h1 : k ≤ 2023 := by
      omega
    have h2024 : k ≤ 2023 := by
      omega
    -- Now we need to derive a contradiction for each k from 2020 to 2023.
    have h2 : ¬ (9 ∣ ∑ i ∈ Finset.Icc 1 k, i * 10 ^ (i - 1)) := by
      have h2024' : k ≤ 2023 := h1
      -- Derive contradiction by checking that none of these values is divisible
      -- Computing the sum for each k and verifying it's not divisible by 9
      interval_cases k <;> try { native_decide }
      <;> norm_num
      <;> tauto
      <;> omega
      <;> tauto
      <;> native_decide
      <;> tauto
      <;> omega
      <;> tauto
      <;> try { native_decide }
      <;> try { try { trivial } <;> try { native_decide } }
    contradiction
    <;> try { contradiction } <;> try { try { tauto } <;> try { omega } }
    <;> try { native_decide }
    <;> try { try { trivial } <;> try { native_decide } }
    <;> try { try { tauto } <;> try { native_decide } }
    <;> try { try { tauto } <;> try { native_decide } }
    <;> try { try { tauto } <;> try { native_decide } }
    all_goals try { tauto }
    all_goals try { native_decide }
    <;> try { native_decide }
    all_goals try { native_decide }