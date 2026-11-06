import Mathlib

theorem algebra_276657 :
    {(P, Q) : ℕ × ℕ | P ∈ Finset.Icc 1 9 ∧ Q ∈ Finset.Icc 1 9 ∧ (P / Q : ℚ) - Q / P = (P + Q) / (P * Q)}.ncard = 8 := by
  have : {(P, Q) : ℕ × ℕ | P ∈ Finset.Icc 1 9 ∧ Q ∈ Finset.Icc 1 9 ∧ (P / Q : ℚ) - Q / P = (P + Q) / (P * Q)} = Finset.filter (fun p : ℕ × ℕ => (p.1 ∈ Finset.Icc 1 9) ∧ (p.2 ∈ Finset.Icc 1 9) ∧ (p.1 / p.2 : ℚ) - (p.2 / p.1 : ℚ) = (p.1 + p.2) / (p.1 * p.2 : ℚ)) (Finset.Icc (0 : ℕ) 9 ×ˢ Finset.Icc (0 : ℕ) 9) := by
    ext ⟨p, q⟩
    simp [Finset.mem_Icc]
    omega
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide