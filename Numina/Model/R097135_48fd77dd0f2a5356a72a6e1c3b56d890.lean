import Mathlib

theorem number_theory_326066 :
    Set.ncard {p : ℕ × ℕ | p.1 ∈ Finset.Icc 1 100 ∧ p.2 ∈ Finset.Icc 1 100 ∧ p.1 ≤ p.2 ∧ 57 ∣ p.1 * p.2} = 228 := by 
  have h1 : {p : ℕ × ℕ | p.1 ∈ Finset.Icc 1 100 ∧ p.2 ∈ Finset.Icc 1 100 ∧ p.1 ≤ p.2 ∧ 57 ∣ p.1 * p.2} = Finset.filter (fun p => 1 ≤ p.1 ∧ p.1 ≤ 100 ∧ 1 ≤ p.2 ∧ p.2 ≤ 100 ∧ p.1 ≤ p.2 ∧ 57 ∣ p.1 * p.2) (Finset.Icc (0 : ℕ) 100 ×ˢ Finset.Icc (0 : ℕ) 100) := by 
    ext ⟨a, b⟩
    simp [Finset.mem_Icc]
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide