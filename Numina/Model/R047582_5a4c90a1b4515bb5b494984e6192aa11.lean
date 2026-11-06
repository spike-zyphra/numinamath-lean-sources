import Mathlib

open Finset Real Nat

theorem number_theory_610797: {n: ℕ | n ≤ 63 ∧ 1 ≤ n ∧ ∑ i ∈ Icc 1 (4 * n), i ∣ ∑ i ∈ Icc 1 (2024 * n), i} = {1,25,63} := by

  have sum1 (k : ℕ) : ∑ i ∈ Icc 1 k, i = k * (k + 1) / 2 := by
    induction k with
    | zero =>
      simp
    | succ k ih =>
      rw [sum_Icc_succ_top (by linarith)]
      simp [ih]
      ring_nf
      omega

  have h1 (n : ℕ) : ∑ i ∈ Icc 1 (4 * n), i = 2 * n * (4 * n + 1) := by
    have h1' : ∑ i ∈ Icc 1 (4 * n), i = (4 * n) * (4 * n + 1) / 2 := by
      apply sum1
    rw [h1']
    ring_nf
    <;> omega

  have h2 (n : ℕ) : ∑ i ∈ Icc 1 (2024 * n), i = 1012 * n * (2024 * n + 1) := by
    have h2' : ∑ i ∈ Icc 1 (2024 * n), i = (2024 * n) * (2024 * n + 1) / 2 := by
      apply sum1
    rw [h2']
    ring_nf
    <;> omega

  have h3 : {n : ℕ | n ≤ 63 ∧ 1 ≤ n ∧ ∑ i ∈ Icc 1 (4 * n), i ∣ ∑ i ∈ Icc 1 (2024 * n), i} ⊆ {1, 25, 63} := by
    intro n hn
    rcases hn with ⟨h₀, h₁, h₂⟩
    have h4 : n ≤ 63 := h₀
    have h5 : 1 ≤ n := h₁

    have h6 : ∑ i ∈ Icc 1 (4 * n), i = 2 * n * (4 * n + 1) := by
      have h1' : ∀ n : ℕ, ∑ i ∈ Icc 1 (4 * n), i = 2 * n * (4 * n + 1) := by
        intro n
        have h1'' : ∑ i ∈ Icc 1 (4 * n), i = (4 * n) * (4 * n + 1) / 2 := by
          apply sum1
        rw [h1'']
        ring_nf
        <;> omega
      specialize h1' n
      simpa using h1'
    have h7 : ∑ i ∈ Icc 1 (2024 * n), i = 1012 * n * (2024 * n + 1) := by
      have h2' : ∀ n : ℕ, ∑ i ∈ Icc 1 (2024 * n), i = 1012 * n * (2024 * n + 1) := by
        intro n
        have h2'' : ∑ i ∈ Icc 1 (2024 * n), i = (2024 * n) * (2024 * n + 1) / 2 := by
          apply sum1
        rw [h2'']
        ring_nf
        <;> omega
      specialize h2' n
      simpa using h2'

    rw [h6] at h₂
    rw [h7] at h₂
    interval_cases n <;> norm_num at h₂ ⊢ <;> omega


  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Forward direction
    intro hn
    rcases hn with ⟨h₀, h₁, h₂⟩
    have h5 : n ≤ 63 := by
      omega
    have h6 : 1 ≤ n := by
      omega
    have h7 : ∑ i ∈ Icc 1 (4 * n), i ∣ ∑ i ∈ Icc 1 (2024 * n), i := by
      omega
    have hn2 : n = 1 ∨ n = 25 ∨ n = 63 := by
      apply h3
      exact ⟨h₀, h₁, h₂⟩
    tauto
  · -- Backward direction
    rintro (rfl | rfl | rfl)
    · -- Show that 1 is in the left side
      refine ⟨by norm_num, by norm_num, ?_⟩
      have h6 : ∑ i ∈ Icc 1 (4 * (1 : ℕ)), i = 2 * 1 * (4 * 1 + 1) := by
        have h1' : ∀ n : ℕ, ∑ i ∈ Icc 1 (4 * n), i = 2 * n * (4 * n + 1) := by
          intro n
          have h1'' : ∑ i ∈ Icc 1 (4 * n), i = (4 * n) * (4 * n + 1) / 2 := by
            apply sum1
          rw [h1'']
          ring_nf
          <;> omega
        specialize h1' 1
        simpa using h1'
      have h7 : ∑ i ∈ Icc 1 (2024 * (1 : ℕ)), i = 1012 * 1 * (2024 * 1 + 1) := by
        have h2' : ∀ n : ℕ, ∑ i ∈ Icc 1 (2024 * n), i = 1012 * n * (2024 * n + 1) := by
          intro n
          have h2'' : ∑ i ∈ Icc 1 (2024 * n), i = (2024 * n) * (2024 * n + 1) / 2 := by
            apply sum1
          rw [h2'']
          ring_nf
          <;> omega
        specialize h2' 1
        simpa using h2'
      rw [h6, h7]
      all_goals norm_num
    · -- Show that 25 is in the left side
      refine ⟨by norm_num, by norm_num, ?_⟩
      have h6 : ∑ i ∈ Icc 1 (4 * (25 : ℕ)), i = 2 * 25 * (4 * 25 + 1) := by
        have h1' : ∀ n : ℕ, ∑ i ∈ Icc 1 (4 * n), i = 2 * n * (4 * n + 1) := by
          intro n
          have h1'' : ∑ i ∈ Icc 1 (4 * n), i = (4 * n) * (4 * n + 1) / 2 := by
            apply sum1
          rw [h1'']
          ring_nf
          <;> omega
        specialize h1' 25
        simpa using h1'
      have h7 : ∑ i ∈ Icc 1 (2024 * (25 : ℕ)), i = 1012 * 25 * (2024 * 25 + 1) := by
        have h2' : ∀ n : ℕ, ∑ i ∈ Icc 1 (2024 * n), i = 1012 * n * (2024 * n + 1) := by
          intro n
          have h2'' : ∑ i ∈ Icc 1 (2024 * n), i = (2024 * n) * (2024 * n + 1) / 2 := by
            apply sum1
          rw [h2'']
          ring_nf
          <;> omega
        specialize h2' 25
        simpa using h2'
      rw [h6, h7]
      all_goals norm_num
    · -- Show that 63 is in the left side
      refine ⟨by norm_num, by norm_num, ?_⟩
      have h6 : ∑ i ∈ Icc 1 (4 * (63 : ℕ)), i = 2 * 63 * (4 * 63 + 1) := by
        have h1' : ∀ n : ℕ, ∑ i ∈ Icc 1 (4 * n), i = 2 * n * (4 * n + 1) := by
          intro n
          have h1'' : ∑ i ∈ Icc 1 (4 * n), i = (4 * n) * (4 * n + 1) / 2 := by
            apply sum1
          rw [h1'']
          ring_nf
          <;> omega
        specialize h1' 63
        simpa using h1'
      have h7 : ∑ i ∈ Icc 1 (2024 * (63 : ℕ)), i = 1012 * 63 * (2024 * 63 + 1) := by
        have h2' : ∀ n : ℕ, ∑ i ∈ Icc 1 (2024 * n), i = 1012 * n * (2024 * n + 1) := by
          intro n
          have h2'' : ∑ i ∈ Icc 1 (2024 * n), i = (2024 * n) * (2024 * n + 1) / 2 := by
            apply sum1
          rw [h2'']
          ring_nf
          <;> omega
        specialize h2' 63
        simpa using h2'
      rw [h6, h7]
      all_goals norm_num