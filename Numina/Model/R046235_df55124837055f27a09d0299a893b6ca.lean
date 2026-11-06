import Mathlib

open Finset Real

theorem algebra_169777 {a : ℕ → ℝ}
    (ha0 : a 0 = 1)
    (han : ∀ n, a (n + 1) = 1 - (n + 1) ^ 2 / (n + 2) ^ 2 * a n) :
    ∀ n, a n = (n + 2) / (2 * (n + 1)) ∧
    (∏ i ∈ range (n + 1), a i) = (n + 2) / 2 ^ (n + 1) := by
  intro n 
  have ha1 : ∀ n, a n = (n + 2) / (2 * (n + 1)) := by
    intro n 
    induction n with 
    | zero =>
      rw [ha0]
      norm_num 
    | succ n ih =>
      have h1 := han n 
      rw [h1, ih]
      field_simp
      ring_nf 
  constructor 
  · -- Show that a_n = (n + 2)/(2*(n + 1))
    specialize ha1 n 
    simpa using ha1 
  · -- Show that the product = (n + 2)/2^(n+1)
    have h2 : ∀ (n : ℕ), ∏ i in range (n + 1), a i = (↑n + 2) / (2 ^ (n + 1)) := by 
      intro n 
      induction n with 
      | zero =>
        simp [ha0]
        all_goals norm_num 
      | succ n ih =>
        rw [prod_range_succ, ih]
        have eq_a_n1 : a (n + 1) = 1 - (↑n + 1) ^ 2 / (↑n + 2) ^ 2 * a n := by
          simpa using han n
        have eq2 : a (n + 1) = (↑n + 3) / (2 * (↑n + 2)) := by
          rw [eq_a_n1]
          rw [ha1 n]
          field_simp
          ring_nf 
        rw [eq2]
        field_simp at *
        <;> ring_nf 
    specialize h2 n 
    simpa using h2