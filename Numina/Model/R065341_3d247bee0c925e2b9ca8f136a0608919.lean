import Mathlib

theorem number_theory_95204 :
    {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ 3 * x + 5 * y = 501}.ncard = 33 := by
  have h1 : {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ 3 * x + 5 * y = 501} = Finset.filter (fun p => p.1 > 0 ∧ p.2 > 0 ∧ 3 * p.1 + 5 * p.2 = 501) (Finset.Icc (0, 0) (167, 100)) := by
    ext ⟨x, y⟩
    simp
    omega
  rw [h1]
  rw [Finset.filter]
  simp [Finset.Icc]
  <;> native_decide