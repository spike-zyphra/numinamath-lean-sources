import Mathlib

theorem number_theory_139175 (n : ℕ) (hn : n = 9440) :
    ∀ i ∈ Finset.Icc n (n + 20), Nat.gcd i 30030 > 1 := by
  rw [hn]
  intro i hi
  have h1 : i ≥ 9440 := by 
    have h2 : i ∈ Finset.Icc (9440 : ℕ) (9440 + 20) := hi
    simp at h2 ⊢
    omega 
  have h2 : i ≤ 9460 := by 
    have h3 : i ∈ Finset.Icc (9440 : ℕ) (9440 + 20) := hi
    simp at h3 ⊢
    omega 
  interval_cases i <;> norm_num 
  <;> try { native_decide }