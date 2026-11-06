import Mathlib

theorem algebra_268737 (n : ℕ) (h : n > 0) (a : ℕ → ℕ)
    (ha : ∀ i ∈ Finset.range 7, a i = n + 7 * i) :
    ∑ i ∈ Finset.range 7, a i = 13524 ↔ n = 1911 := by
  have h1 : ∑ i ∈ Finset.range 7, a i = 7 * n + 147 := by
    simp [Finset.sum_range_succ, ha]
    <;> ring_nf <;> omega
  rw [h1]
  constructor
  · -- Forward direction: sum equals 13524 implies n equals 1911
    intro h2
    omega
  · -- Backward direction: n equals 1911 implies sum equals 13524
    intro h3
    subst h3
    all_goals norm_num