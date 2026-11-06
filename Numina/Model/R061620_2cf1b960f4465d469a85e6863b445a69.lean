import Mathlib

theorem number_theory_279348 :
    Set.ncard {(m, n) : ℕ × ℕ | 1 ≤ m ∧ m ≤ 99 ∧ 1 ≤ n ∧ n ≤ 99 ∧ IsSquare ((m + n) ^ 2 + 3 * m + n)} = 98 := by
  have h1 : {(m, n) : ℕ × ℕ | 1 ≤ m ∧ m ≤ 99 ∧ 1 ≤ n ∧ n ≤ 99 ∧ IsSquare ((m + n) ^ 2 + 3 * m + n)} = Finset.filter (fun p => 1 ≤ p.1 ∧ p.1 ≤ 99 ∧ 1 ≤ p.2 ∧ p.2 ≤ 99 ∧ IsSquare ((p.1 + p.2) ^ 2 + 3 * p.1 + p.2)) (Finset.Icc (0 : ℕ) 99 ×ˢ Finset.Icc (0 : ℕ) 99) := by
    ext ⟨m, n⟩
    simp
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide