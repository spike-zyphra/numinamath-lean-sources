import Mathlib

theorem algebra_227851 {n : ℕ} (hn : 0 < n) (ε : ℂ) (hε : ε ^ n = 1)
    (hε1 : ∀ j < n, ε ^ j ≠ 1) (k : ℕ) :
    ∑ i ∈ Finset.range n, ε ^ (i * k) = if k ∈ Finset.Icc 1 (n - 1) then 0 else n := by
  have h1 : ε ^ 0 = 1 := by
    simp
  have h2 := hε1 0 (by linarith)
  have h3 : ε ^ 0 = 1 := by
    simp
  contradiction