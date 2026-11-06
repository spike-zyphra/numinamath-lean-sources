import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

theorem number_theory_360 :
  IsLeast {n | ∃ x : Fin 7 → ℕ, (∀ i j, i < j → x i < x j) ∧ (∑ i, x i) = 2015 ∧ n = x 3 + x 4 + x 5 + x 6} 1158 := by
  constructor
  · -- Show that 1158 is achievable.
    use λ i =>
      match i with
      | 0 => 284
      | 1 => 286
      | 2 => 287
      | 3 => 288
      | 4 => 289
      | 5 => 290
      | 6 => 291
      | _ => 0
    constructor
    · -- Show the sequence is strictly increasing
      intro i j h
      fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
    constructor
    · -- Show the sum is 2015
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
      <;> try native_decide
    · -- Show that n = x 3 + x 4 + x 5 + x 6
      simp
  · -- Show that 1158 is minimal
    intro n hn
    rcases hn with ⟨x, hx1, hx2, hx3⟩
    have h1 := hx1 0 1 (by simp)
    have h2 := hx1 1 2 (by simp)
    have h3 := hx1 2 3 (by simp)
    have h4 := hx1 3 4 (by simp)
    have h5 := hx1 4 5 (by simp)
    have h6 := hx1 5 6 (by simp)
    simp at h1 h2 h3 h4 h5 h6
    have h7 : x 0 < x 1 := h1
    have h8 : x 1 < x 2 := h2
    have h9 : x 2 < x 3 := h3
    have h10 : x 3 < x 4 := h4
    have h11 : x 4 < x 5 := h5
    have h12 : x 5 < x 6 := h6
    have h3 : ∑ i : Fin 7, x i = 2015 := hx2
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at h3
    have h4 : x 3 + x 4 + x 5 + x 6 ≥ 1158 := by
      omega
    linarith [hx3, h4]