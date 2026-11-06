import Mathlib

theorem number_theory_238786 :
    Set.ncard {N : ℕ | N > 0 ∧ ((∃ k, N = k ∧ k ∈ Finset.Icc 1000 9999) ∧ ¬(∃ m, N + 20 = m ∧ m ∈ Finset.Icc 1000 9999)) ∨ (¬(∃ k, N = k ∧ k ∈ Finset.Icc 1000 9999) ∧ ∃ m, N + 20 = m ∧ m ∈ Finset.Icc 1000 9999)} = 40 := by
  have h1 : {N : ℕ | N > 0 ∧ ((∃ k, N = k ∧ k ∈ Finset.Icc 1000 9999) ∧ ¬(∃ m, N + 20 = m ∧ m ∈ Finset.Icc 1000 9999)) ∨ (¬(∃ k, N = k ∧ k ∈ Finset.Icc 1000 9999) ∧ ∃ m, N + 20 = m ∧ m ∈ Finset.Icc 1000 9999)} = Finset.filter (fun N => N > 0 ∧ ((N ∈ Finset.Icc 1000 9999 ∧ ¬(N + 20 ∈ Finset.Icc 1000 9999)) ∨ (N ∉ Finset.Icc 1000 9999 ∧ N + 20 ∈ Finset.Icc 1000 9999))) (Finset.Icc 0 10019) := by
    ext N
    simp
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide