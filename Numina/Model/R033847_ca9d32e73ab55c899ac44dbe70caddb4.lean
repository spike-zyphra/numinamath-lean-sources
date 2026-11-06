import Mathlib

theorem algebra_274540 :
    {(p, q) : ℕ × ℕ | p > 0 ∧ q > 0 ∧ p + q ≤ 100 ∧ (p + 1 / (q : ℚ)) / (1 / p + q) = 17}.ncard = 5 := by
  have h1 : {(p, q) : ℕ × ℕ | p > 0 ∧ q > 0 ∧ p + q ≤ 100 ∧ (p + 1 / (q : ℚ)) / (1 / p + q) = 17} = Finset.filter (fun s : ℕ × ℕ => (s.1 > 0 ∧ s.2 > 0 ∧ s.1 + s.2 ≤ 100 ∧ ((s.1 + 1 / (s.2 : ℚ)) / (1 / (s.1 : ℚ) + (s.2 : ℚ)) = 17))) (Finset.Icc (0 : ℕ) 100 ×ˢ Finset.Icc (0 : ℕ) 100) := by
    ext ⟨p, q⟩
    simp
    intro hp hq heq heqeq
    have h2 : p ≤ 100 := by
      linarith
    have h3 : q ≤ 100 := by
      linarith
    simp [h2, h3] at *
    <;> try { tauto }
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide