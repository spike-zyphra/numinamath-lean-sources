import Mathlib

theorem algebra_100171 (a : ℕ → ℝ) (h₀ : ∑ i ∈ Finset.range 100, a i = 2022 * 100)
    (h₁ : ∑ i ∈ Finset.range 100, a (i + 1) = 2023 * 100) (h₂ : a 0 + a 100 = 51 * 2) :
    ∑ i ∈ Finset.range 101, a i = 202301 := by
  have eq1 : ∑ i ∈ Finset.range 100, a i = 202200 := by
    linarith

  have eq2 : ∑ i ∈ Finset.range 100, a (i + 1) = 202300 := by
    linarith

  have eq3 : ∑ i ∈ Finset.range 101, a i = ∑ i ∈ Finset.range 100, a i + a 100 := by
    rw [Finset.sum_range_succ]

  have eq7 : a 100 - a 0 = 100 := by
    have h8 : ∑ i ∈ Finset.range 101, a i = a 0 + (∑ i ∈ Finset.range 100, a (i + 1)) := by
      simp [Finset.sum_range_succ, Finset.sum_range_succ]
      <;> linarith
    have h9 : ∑ i ∈ Finset.range 101, a i = (∑ i ∈ Finset.range 100, a i) + a 100 := eq3
    linarith [h8, h9, eq1, eq2]

  have h10 : a 100 = 101 := by 
    nlinarith [h₂, eq7]

  have h12 : ∑ i ∈ Finset.range 101, a i = 202301 := by
    linarith [eq3, eq1, h10]

  exact h12