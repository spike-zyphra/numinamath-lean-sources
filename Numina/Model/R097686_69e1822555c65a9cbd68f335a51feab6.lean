import Mathlib

theorem number_theory_78071 : {k : ℕ | 0 ≤ k ∧ k ≤ 2014 ∧ 4 ∣ Nat.choose 2014 k}.encard = 991 := by
  have h1 : {k : ℕ | 0 ≤ k ∧ k ≤ 2014 ∧ 4 ∣ Nat.choose 2014 k} = Finset.filter (λ k => 4 ∣ Nat.choose 2014 k) (Finset.Icc (0 : ℕ) 2014) := by
    ext k
    simp
    <;> tauto

  rw [h1]
  rw [Finset.filter]
  simp [Finset.Icc]
  native_decide