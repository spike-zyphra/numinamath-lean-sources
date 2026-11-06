import Mathlib

theorem number_theory_300917 :
    {(m, n) : ℕ × ℕ | 1 ≤ m ∧ m ≤ n ∧ n ≤ 30 ∧ 21 ∣ m * n}.ncard = 57 := by 
  have h1 : {(m, n) : ℕ × ℕ | 1 ≤ m ∧ m ≤ n ∧ n ≤ 30 ∧ 21 ∣ m * n} = Finset.filter (fun p : ℕ × ℕ => 1 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 30 ∧ 21 ∣ p.1 * p.2) (Finset.Icc (0 : ℕ) 30 ×ˢ Finset.Icc (0 : ℕ) 30) := by
    ext ⟨m, n⟩
    simp
    <;> try { omega }
    <;> try { 
      tauto 
    }
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide