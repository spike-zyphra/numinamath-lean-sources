import Mathlib

theorem algebra_152355 (n : ℕ) (h : n % 2 = 0) (h' : (100 - 2) * 50 = ∑ i ∈ Finset.Icc 1 100 \ {n, n + 2}, i) :
    n * (n + 2) = 5624 := by
  have h1 : n ≤ 100 := by
    by_contra h2
    push_neg at h2
    have h2' : n > 100 := by omega
    have h3 : n ≥ 101 := by omega
    have h4 : n + 2 ≥ 103 := by omega
    have h5 : ∑ i in Finset.Icc 1 100 \ {n, n + 2}, i = ∑ i in Finset.Icc 1 100, i := by
      have h6 : (Finset.Icc 1 100 : Finset ℕ) \ {n, n + 2} = Finset.Icc 1 100 := by
        ext i
        simp
        omega
      rw [h6]
    rw [h5] at h'
    have h7 : ∑ i in Finset.Icc 1 100, i = 5050 := by
      native_decide
    rw [h7] at h'
    all_goals
      omega
  have h9 : n ≤ 100 := by omega
  interval_cases n <;> try { 
    contradiction 
  } 
  <;> try { 
    native_decide 
  }