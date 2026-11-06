import Mathlib

theorem number_theory_168479 :
    {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ 6 * a + 10 * b + 15 * c = 3000}.ncard = 4851 := by
  have : {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ 6 * a + 10 * b + 15 * c = 3000} = Finset.filter (λ s => (s.1 > 0 ∧ s.2.1 > 0 ∧ s.2.2 > 0 ∧ 6 * s.1 + 10 * s.2.1 + 15 * s.2.2 = 3000)) (Finset.Icc (0, 0, 0) (500, 300, 200)) := by
    ext ⟨a, b, c⟩
    simp
    omega
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide