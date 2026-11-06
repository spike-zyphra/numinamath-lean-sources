import Mathlib

theorem algebra_9321 (m n : ℤ) (hm : m > 0) (hn : n ≠ 0) (h : ∃ x y, x ∈ Set.Ioo 0 1 ∧ y ∈ Set.Ioo 0 1 ∧ x ≠ y ∧ m * x ^ 2 + n * x + 2 = 0 ∧ m * y ^ 2 + n * y + 2 = 0) :
    m ≥ 6 := by 
  rcases h with ⟨x, y, hx, hy, hne, heq1, heq2⟩
  rw [Set.mem_Ioo] at hx hy
  have h1 : x > 0 := hx.1
  have h2 : x < 1 := hx.2
  have h3 : y > 0 := hy.1
  have h4 : y < 1 := hy.2
  omega