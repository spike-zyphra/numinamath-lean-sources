import Mathlib

theorem number_theory_290861 (m n : ℕ) (hm : m > 0) (hn : n > 0)
    (h : ∑ i ∈ Finset.range (15 * m), (2 * i + 2) + ∑ j ∈ Finset.range n, (2 * j + 1) = 1987) :
    3 * m + 4 * n ≤ 221 := by
  have heven : ∀ m : ℕ, ∑ i in Finset.range (15 * m), (2 * i + 2) = 15 * m * (15 * m + 1) := by
    intro m
    induction m with 
    | zero => 
      simp
    | succ m ih =>
      rw [show 15 * (m + 1) = 15 * m + 15 by omega]
      rw [Finset.sum_range_add]
      rw [ih]
      simp [Finset.sum_range_succ, add_mul, mul_add]
      ring_nf
  have hodd : ∀ n : ℕ, ∑ j in Finset.range n, (2 * j + 1) = n ^ 2 := by 
    intro n 
    induction n with 
    | zero => 
      simp 
    | succ n ih => 
      rw [Finset.sum_range_succ, ih] 
      ring 
  have h1 : 15 * m * (15 * m + 1) + n ^ 2 = 1987 := by 
    rw [heven m, hodd n] at h 
    all_goals nlinarith
  by_contra h2 
  push_neg at h2 
  have h2 : 3 * m + 4 * n > 221 := by linarith
  have h2 : m ≤ 3 := by 
    nlinarith [show 15 * m * (15 * m + 1) + n ^ 2 = 1987 from h1]
  have h3 : n ≤ 44 := by 
    nlinarith [show 15 * m * (15 * m + 1) + n ^ 2 = 1987 from h1]
  interval_cases m <;> interval_cases n <;> omega