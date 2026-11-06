import Mathlib

theorem number_theory_189958 :
    Set.ncard {x : ℕ | x ∈ Finset.Icc 1 16500 ∧ ¬ 5 ∣ x} = 13200 ∧
    Set.ncard {x : ℕ | x ∈ Finset.Icc 1 16500 ∧ ¬ 5 ∣ x ∧ ¬ 3 ∣ x} = 8800 ∧
    Set.ncard {x : ℕ | x ∈ Finset.Icc 1 16500 ∧ ¬ 5 ∣ x ∧ ¬ 3 ∣ x ∧ ¬ 11 ∣ x} = 8000 := by
  constructor
  · -- Prove the first statement about numbers not divisible by 5
    have h1 : {x : ℕ | x ∈ Finset.Icc 1 16500 ∧ ¬ 5 ∣ x} = Finset.filter (λ x => ¬ 5 ∣ x) (Finset.Icc 1 16500) := by
      ext n
      simp
    rw [h1]
    rw [Set.ncard_coe_Finset]
    native_decide
  constructor
  · -- Prove the second statement about numbers not divisible by 5 or 3
    have h2 : {x : ℕ | x ∈ Finset.Icc 1 16500 ∧ ¬ 5 ∣ x ∧ ¬ 3 ∣ x} = Finset.filter (λ x => ¬ 5 ∣ x ∧ ¬ 3 ∣ x) (Finset.Icc 1 16500) := by
      ext n
      simp
    rw [h2]
    rw [Set.ncard_coe_Finset]
    native_decide
  · -- Prove the third statement about numbers not divisible by 5, 3, or 11
    have h3 : {x : ℕ | x ∈ Finset.Icc 1 16500 ∧ ¬ 5 ∣ x ∧ ¬ 3 ∣ x ∧ ¬ 11 ∣ x} = Finset.filter (λ x => ¬ 5 ∣ x ∧ ¬ 3 ∣ x ∧ ¬ 11 ∣ x) (Finset.Icc 1 16500) := by
      ext n
      simp
    rw [h3]
    rw [Set.ncard_coe_Finset]
    native_decide