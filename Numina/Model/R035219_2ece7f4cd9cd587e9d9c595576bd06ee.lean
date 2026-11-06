import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_299196 {a : ℝ} (ha : 0 ≤ a) :
    IsLeast {x | ∃ t : Fin 7 → ℝ, (∀ i, 0 ≤ t i) ∧ (∑ i, t i) = a ∧
      x = max (max (max (max (t 0 + t 1 + t 2) (t 1 + t 2 + t 3)) (t 2 + t 3 + t 4)) (t 3 + t 4 + t 5)) (t 4 + t 5 + t 6)} (a / 3) := by
  constructor
  · -- Show that a/3 is in the set
    use (fun i =>
      match i with 
        | 0 | 3 | 6 => a / 3
        | _ => (0 : ℝ)
      )
    constructor
    · intro i
      fin_cases i <;> simp <;> nlinarith
    constructor
    · simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, le_of_lt]
      <;> ring_nf <;> linarith [ha]
    · simp [max_eq_left_of_lt, max_eq_right_of_lt, add_assoc]
      <;> ring_nf <;> simp [ha]
      <;> norm_num <;> linarith [ha]
  · -- Show that a/3 is the least in the set
    rintro x ⟨t, ht_nonneg, ht_sum, hx⟩
    have h1 : x = max (max (max (max (t 0 + t 1 + t 2) (t 1 + t 2 + t 3)) (t 2 + t 3 + t 4)) (t 3 + t 4 + t 5)) (t 4 + t 5 + t 6) := by
      linarith
    have h2 : t 0 + t 1 + t 2 ≤ x := by
      simp [h1] at *
      <;> try { linarith }
    have h3 : t 1 + t 2 + t 3 ≤ x := by 
      simp [h1] at *
      <;> try { linarith }
    have h4 : t 2 + t 3 + t 4 ≤ x := by
      simp [h1] at *
      <;> try { linarith }
    have h5 : t 3 + t 4 + t 5 ≤ x := by
      simp [h1] at *
      <;> try { linarith }
    have h6 : t 4 + t 5 + t 6 ≤ x := by 
      simp [h1] at *
      <;> try { linarith }
    have h7 : t 0 + t 1 + t 2 + t 3 + t 4 + t 5 + t 6 = a := by
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at ht_sum ⊢
      <;> linarith 
    linarith [h7, h2, h3, h4, h5, h6, ht_nonneg 0, ht_nonneg 1, ht_nonneg 2, ht_nonneg 3, ht_nonneg 4, ht_nonneg 5, ht_nonneg 6]