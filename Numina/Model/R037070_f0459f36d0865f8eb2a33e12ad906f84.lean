import Mathlib

theorem number_theory_272261 (m : ℕ) (hm : ∀ n, ∃ k, k ∈ Finset.Icc n (n + m - 1) ∧ (Nat.digits 10 k).sum ≡ 0 [MOD 6]) :
    m ≥ 9 := by
  by_contra h
  push_neg at h
  have h1 := hm 9999997
  rcases h1 with ⟨k, hk1, hk2⟩
  have h2 : k ≥ 9999997 := by
    simp [Finset.mem_Icc] at hk1
    omega
  have h3 : k ≤ 9999997 + m - 1 := by
    simp [Finset.mem_Icc] at hk1
    omega
  have h4 : m ≤ 8 := by
    omega
  have h5 : k ≤ 10000004 := by
    have h6 : m ≤ 8 := by
      omega
    have h7 : k ≤ 9999997 + m - 1 := by
      simp [Finset.mem_Icc] at hk1
      omega
    omega
  interval_cases k <;> norm_num [Nat.ModEq] at hk2
  all_goals
    omega