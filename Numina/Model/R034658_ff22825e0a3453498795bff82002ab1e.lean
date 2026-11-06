import Mathlib

theorem number_theory_93323 (n : ℕ) (h₀ : n < 100) (h₁ : n > 9)
    (h₂ : {k | k = 1 ∧ Nat.Prime n ∨ k = 2 ∧ Even n ∨ k = 3 ∧ 7 ∣ n ∨ k = 4 ∧ (Nat.digits 10 n).contains 9}.encard = 3) :
    n % 10 = 8 := by
  have h4 : n < 100 := by linarith
  have h5 : n > 9 := h₁
  have h3 : n ≤ 99 := by linarith
  have h6 : {k | k = 1 ∧ Nat.Prime n ∨ k = 2 ∧ Even n ∨ k = 3 ∧ 7 ∣ n ∨ k = 4 ∧ (Nat.digits 10 n).contains 9} = Finset.filter (fun (k : ℕ) => k = 1 ∧ Nat.Prime n ∨ k = 2 ∧ Even n ∨ k = 3 ∧ 7 ∣ n ∨ k = 4 ∧ (Nat.digits 10 n).contains 9) (Finset.Icc 1 4) := by
    ext k
    simp
    omega
  rw [h6] at h₂
  rw [Set.encard_coe_eq_coe_finsetCard] at h₂
  interval_cases n <;> norm_num [Finset.filter, Finset.card, Nat.Prime, Nat.even_iff, Nat.mul_comm] at h₂ ⊢
  <;> all_goals
    try { contradiction }
    <;> try { simp_all }
    <;> try { native_decide }
    <;> try { tauto }
  <;> all_goals
    try { tauto }
    <;> try { norm_num }
    <;> try { 
      exfalso
      <;> try { trivial }
    }
  <;> try { norm_num }
  <;> try { tauto }