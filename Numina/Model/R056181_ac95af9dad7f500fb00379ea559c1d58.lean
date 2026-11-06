import Mathlib

theorem other_79341 (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (a : Fin (m + 2) → Fin (n + 2) → ℝ)
    (h : ∀ i j, i ≠ 0 → j ≠ 0 → a i j = (a (i - 1) j + a (i + 1) j + a i (j - 1) + a i (j + 1)) / 4) :
    ∃ b : Fin m → Fin n → ℝ,
      ∀ i j, b i j = (a (i + 1) j + a (i - 1) j + a i (j + 1) + a i (j - 1)) / 4 := by 
  use λ i j => (a (i + 1) j + a (i - 1) j + a i (j + 1) + a i (j - 1)) / 4 
  all_goals simp 
  <;> try { tauto }