import Mathlib

theorem number_theory_179355 :
    ¬∃ z : ℕ, ∃ n : ℕ, z = n^2 ∧ z ∈ Finset.Icc 1000 9999 ∧ (z / 100) % 10 = (z % 100) % 10 ∧
      (z / 10) % 10 = (z / 1000) % 10 := by 
  rintro ⟨z, ⟨n, hz, h1, h2, h3⟩⟩
  rw [Finset.mem_Icc] at h1
  rcases h1 with ⟨h1l, h1u⟩
  have h32 : n ≥ 32 := by
    by_contra h
    push_neg at h
    have hn : n ≤ 31 := by omega
    have hz' : n ^ 2 ≤ 31 ^ 2 := by
      have : n ≤ 31 := hn
      nlinarith [sq_nonneg (n - 31)]
    nlinarith
  have h99 : n ≤ 99 := by
    by_contra h
    push_neg at h
    have hn : n ≥ 100 := by omega
    have hz : n^2 ≥ 100 ^ 2 := by 
      nlinarith [sq_nonneg (n - 100)]
    nlinarith
  interval_cases n <;> norm_num [hz] at *
  <;> omega