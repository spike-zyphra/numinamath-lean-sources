import Mathlib

open Finset

theorem number_theory_49276 {f : ℕ → ℕ}
    (hf : ∀ x, f x = ∑ i ∈ (Ico 1 x).filter (fun j => Nat.Coprime j x), i) :
    ∀ m n, Odd n → ∃ x, m ∣ x ∧ ∃ k, (f x) = k ^ n := by
  intro m n hn
  use 0
  constructor
  · -- Show m divides 0
    use 0
    all_goals omega
  · -- Show exists k, f 0 = k^n
    use 0
    have h1 : f 0 = 0 := by 
      rw [hf]
      simp [Finset.sum_eq_zero]
    rw [h1]
    have h2 : n ≥ 1 := by 
      obtain ⟨k, hk⟩ := hn
      omega
    have h3 : (0 : ℕ) ^ n = 0 := by 
      apply Nat.zero_pow
      omega
    rw [h3]
    all_goals omega