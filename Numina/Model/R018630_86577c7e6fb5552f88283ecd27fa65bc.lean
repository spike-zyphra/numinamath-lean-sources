import Mathlib


theorem number_theory_102039 (n : ℕ) (h₀ : n ∈ Finset.Icc 10000 99999) (h₁ : Nat.digits 10 n = List.reverse (Nat.digits 10 n))
    (h₂ : ∃ m, m ∈ Finset.Icc 1000 9999 ∧ Nat.digits 10 m = List.reverse (Nat.digits 10 m) ∧ n = 45 * m) :
    n ≤ 59895 := by
  rcases h₂ with ⟨m, hm1, hm2, hn⟩
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₃, h₄⟩
  rw [Finset.mem_Icc] at hm1
  rcases hm1 with ⟨h₅, h₆⟩
  by_contra h
  push_neg at h
  have h7 : m > 1331 := by
    omega
  have h8 : m ≤ 2222 := by
    omega
  interval_cases m <;> norm_num [hn] at h₁ ⊢
  <;> all_goals omega