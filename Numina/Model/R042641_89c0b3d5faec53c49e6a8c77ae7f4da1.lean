import Mathlib

open Finset

theorem number_theory_4475 (n : ℕ) :
    ∏ j ∈ Icc 1 n, 2^j = 2^(n * (n + 1) / 2) := by
  have h1 : ∀ n : ℕ, ∏ j ∈ Icc 1 n, 2^j = 2 ^ (∑ j ∈ Icc 1 n, j) := by
    intro n
    induction n with
    | zero =>
      simp
    | succ k ih =>
      rw [prod_Icc_succ_top, ih]
      rw [← pow_add]
      rw [sum_Icc_succ_top]
      simp [add_assoc] at *
      all_goals
        try { omega }
        <;> try { trivial }
        <;> try { tauto }
        <;> try { nlinarith }
  rw [h1]
  have h2 : ∀ n : ℕ, ∑ i ∈ Icc 1 n, i = n * (n + 1) / 2 := by
    intro n
    induction n with
    | zero =>
      simp
    | succ k ih =>
      rw [sum_Icc_succ_top, ih]
      all_goals
        ring_nf at *
        <;> omega
  rw [h2 n]
  all_goals
    try { trivial }
    <;> try { tauto }
    <;> try { ring_nf <;> omega }
    all_goals
      try { trivial }
      <;> try { tauto }
      <;> try { ring_nf <;> omega }
      all_goals
        try { trivial }
        <;> try { tauto }
        <;> try { ring_nf <;> omega }