import Mathlib

theorem number_theory_243289 (n : ℕ) (h : n ∈ Finset.Icc 100 999) :
    n = (Nat.digits 10 n).sum ^ 3 ↔ n = 512 := by 
  rw [Finset.mem_Icc] at h
  rcases h with ⟨hn1, hn2⟩
  constructor
  · -- Assume n = (Nat.digits 10 n).sum ^ 3, prove n = 512
    intro h_eq
    interval_cases n <;> norm_num at h_eq ⊢ 
      <;> norm_num [Nat.digits, Nat.digitsAux] at h_eq ⊢
      <;> tauto 
      <;> omega
  · -- Assume n = 512, prove n = (Nat.digits 10 n).sum ^ 3
    intro h_eq
    rw [h_eq]
    all_goals native_decide 
    <;> tauto