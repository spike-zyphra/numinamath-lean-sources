import Mathlib

open Finset

theorem number_theory_641141 (N : ℕ) (hN : N > 0) :
  ∑ d ∈ N.divisors, (1 : ℚ) / d = (∑ d ∈ N.divisors, d) / N := by 
  norm_num
  rw [sum_div]
  -- use the sum_nbij' to prove that these two sum is equal, namely, `∑ x ∈ N.divisors, (↑x)⁻¹ = ∑ i ∈ N.divisors, ↑i / ↑N`.
  let t : ℕ → ℕ := fun n => N / n
  refine sum_nbij' t t ?_ ?_ ?_ ?_ ?_ 
  · simp
    unfold t 
    intro d hd1 hn
    constructor
    · use d
      exact Eq.symm (Nat.div_mul_cancel hd1)
    · exact hn
  · simp 
    unfold t
    intro d hd1 hn
    constructor
    · use d
      exact Eq.symm (Nat.div_mul_cancel hd1)
    · exact hn
  · simp 
    unfold t
    intro d hd1 hn 
    exact Nat.div_div_self hd1 hn
  · simp 
    unfold t
    intro d hd1 hn 
    exact Nat.div_div_self hd1 hn
  · simp
    unfold t
    intro d hd1 hn 
    obtain ⟨k, hk⟩ := hd1
    rw [hk]
    field_simp
    have neq1 : (d : ℚ) ≠ 0 := by 
      norm_cast
      by_contra hc
      rw [hc] at hk
      simp at hk
      exact hn hk
    have neq2 : (k : ℚ) ≠ 0 := by 
      norm_cast
      by_contra hc
      rw [hc] at hk
      simp at hk
      exact hn hk
    field_simp