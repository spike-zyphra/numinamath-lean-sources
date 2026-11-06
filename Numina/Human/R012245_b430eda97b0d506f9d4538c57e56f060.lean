import Mathlib

open Finset

theorem number_theory_192221  :
  ∃ k, ∃ m ,  ∑ i ∈ Finset.range 100, (2 : ℝ) ^ (k + i) = ∑ i ∈ Finset.range m, ((i : ℝ) + 1):= by 
  use 99, (2 ^ 100 - 1)
  have aux1 : ∑ i ∈ Finset.range 100, (2 : ℕ) ^ (99 + i)  
    = 2 ^ 99 * (2 ^ 100 - 1) := by
    simp_rw [pow_add]
    rw [←Finset.mul_sum]
    congr
  have aux1' : ∑ i ∈ Finset.range 100, (2 : ℝ) ^ (99 + i)  
    = 2 ^ 99 * (2 ^ 100 - 1) := by norm_cast
  have aux2 : ∑ i ∈ Finset.range (2 ^ 100 - 1), ((i : ℝ) + 1) 
    = 2 ^ 99 * (2 ^ 100 - 1)  := by 
    have aux (n : ℕ) : ∑ i ∈ Finset.range n, ((i : ℝ) + 1) = 
      (n + 1) * n / 2 := by 
      induction n with
      | zero => simp
      | succ k ih => 
        have insert_aux : range (k + 1) = 
          insert k (range k) := by 
          exact range_add_one
        rw [insert_aux]
        rw [sum_insert]
        rw [ih]
        field_simp
        ring
        simp
    obtain h := aux (2 ^ 100 - 1)
    rw [h]
    norm_num
  rw [aux1', aux2]