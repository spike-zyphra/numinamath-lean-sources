import Mathlib

theorem number_theory_115734 :
    {(m, n, p) : ℕ × ℕ × ℕ | m ≤ 5 ∧ n ≤ 5 ∧ p ≤ 5 ∧ m ≠ 0 ∧ n ≠ 0 ∧ p ≠ 0 ∧ 10 ∣ 2^m + 3^n + 5^p}.ncard = 35 := by
  have : {(m, n, p) : ℕ × ℕ × ℕ | m ≤ 5 ∧ n ≤ 5 ∧ p ≤ 5 ∧ m ≠ 0 ∧ n ≠ 0 ∧ p ≠ 0 ∧ 10 ∣ 2^m + 3^n + 5^p} = Finset.filter (fun s : ℕ × ℕ × ℕ => 
      let (m, n, p) := s
      m ≤ 5 ∧ n ≤ 5 ∧ p ≤ 5 ∧ m ≠ 0 ∧ n ≠ 0 ∧ p ≠ 0 ∧ 10 ∣ 2^m + 3^n + 5^p
    ) (Finset.Icc (0 : ℕ) 5 ×ˢ Finset.Icc (0 : ℕ) 5 ×ˢ Finset.Icc (0 : ℕ) 5) := by
    ext ⟨m, n, p⟩
    simp
    <;> omega
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide