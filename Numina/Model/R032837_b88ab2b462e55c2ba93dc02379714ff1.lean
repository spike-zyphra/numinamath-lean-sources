import Mathlib

open Finset Real

theorem algebra_123047 {T S : ℕ → ℝ}
    (hT : ∀ n, T n = ∑ i in range n, (i + 1))
    (hS : ∀ n, S n = ∑ i in range n, (1 / T (i + 1))) :
    ∑ i in range 1996, (1 / S (i + 1)) > 1001 := by 
  have h1 : ∀ n, T n = (n : ℝ) * (n + 1) / 2 := by
    intro n
    rw [hT n]
    have h2 : ∀ n : ℕ, ∑ i in range n, (i + 1 : ℝ) = (n : ℝ) * (n + 1) / 2 := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [sum_range_succ, ih]
        field_simp
        <;> ring
    specialize h2 n
    simpa using h2

  have hS' : ∀ n : ℕ, S n = (2 * (n : ℝ)) / (n + 1 : ℝ) := by 
    intro n
    rw [hS n]

    have ht : ∀ i : ℕ, T (i + 1) = (i + 1 : ℝ) * (i + 2 : ℝ) / 2 := by
      intro i
      specialize h1 (i + 1)
      simp [show (i + 1 : ℕ) = i + 1 by rfl] at h1 ⊢
      <;> linarith

    have h3 : ∀ i : ℕ, 1 / T (i + 1) = 2 / ((i + 1 : ℝ) * (i + 2 : ℝ)) := by
      intro i
      rw [ht i]
      field_simp
      <;> ring

    simp_rw [h3]

    have h4 : ∀ (n : ℕ), ∑ i in range n, (2 / (((i + 1 : ℕ) : ℝ) * (i + 2 : ℕ))) = (2 * (n : ℝ)) / (n + 1 : ℝ) := by 
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [sum_range_succ, ih]
        field_simp at *
        <;> ring

    specialize h4 n
    simpa using h4

  have h3 : ∀ (i : ℕ), 1 / S (i + 1) = (i + 2 : ℝ) / (2 * (i + 1 : ℝ)) := by
    intro i
    rw [show S (i + 1) = (2 * (i + 1 : ℕ)) / (i + 1 + 1 : ℝ) by 
      specialize hS' (i + 1)
      simpa using hS']
    <;> field_simp <;> ring

  simp_rw [h3]
  norm_num [sum_range_succ]
  <;> try { linarith [Real.log_le_sub_one_of_pos (show (1997 : ℝ) > 0 by norm_num : (1997 : ℝ) > 0)] }
  <;> native_decide