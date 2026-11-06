import Mathlib

theorem number_theory_202371 (n : ℕ) (h₀ : n ∈ Finset.Icc 10000 99999) (h₁ : Nat.digits 10 n = List.reverse (Nat.digits 10 n))
    (h₂ : ∃ m, m ∈ Finset.Icc 1000 9999 ∧ Nat.digits 10 m = List.reverse (Nat.digits 10 m) ∧ n = 45 * m) :
    n ≤ 59895 := by
  rcases h₂ with ⟨m, hm, hm_pal, hn⟩
  rw [Finset.mem_Icc] at hm
  rcases hm with ⟨hm1, hm2⟩
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨hn1, hn2⟩
  by_contra h
  push_neg at h
  have h5 : n > 59895 := by
    omega
  have h6 : 45 * m > 59895 := by
    omega
  have h7 : m > 1331 := by
    omega
  have h8 : m ≤ 2222 := by
    nlinarith
  interval_cases m <;> norm_num [hn] at h₁ h5 h6 h7 h8 ⊢ <;> all_goals
    omega