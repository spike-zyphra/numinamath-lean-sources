import Mathlib

theorem number_theory_81323 (n : ℕ) (hn : Odd n ∧ n ≥ 3) (a : Fin n → ℝ)
    (h : ∀ i j, ∃ k : ℤ, Real.sqrt ((a i - a j)^2) = k)
    (h' : ∀ i, Even (∑ j : Fin n, if j ≠ i then Real.sqrt ((a i - a j)^2) else 0)) :
    ∀ i j, Even (Real.sqrt ((a i - a j)^2)) := by
  intro i j
  have h1 : ∃ k : ℤ, Real.sqrt ((a i - a j) ^ 2) = ↑k := h i j
  rcases h1 with ⟨k, hk⟩
  rw [show Real.sqrt ((a i - a j)^2) = (↑k : ℝ) by linarith [hk]]
  refine' ⟨k / 2, by simp [Int.even_iff] at *⟩