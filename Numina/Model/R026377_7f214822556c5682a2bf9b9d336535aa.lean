import Mathlib

open Real Set
open scoped Topology

theorem algebra_216625 (f : ℝ → ℝ) (hf : f = λ x => 2020 * x / (x ^ 2 + x + 1)) :
    range f = {y | -2020 ≤ y ∧ y ≤ 2020 / 3} := by
  ext y
  simp [hf, mem_range]
  constructor
  · -- Assume y ∈ range f, so there exists x such that f(x) = y
    rintro ⟨x, hy⟩
    have h1 : x ^ 2 + x + 1 > 0 := by
      nlinarith [sq_nonneg (x + 1 / 2)]
    have eq1 : 2020 * x = y * (x ^ 2 + x + 1) := by
      have hne : x ^ 2 + x + 1 ≠ 0 := by
        nlinarith [sq_nonneg (x + 1 / 2)]
      field_simp [hne] at hy ⊢
      linarith
    have eq2 : y * (x ^ 2) + (y - 2020) * x + y = 0 := by
      nlinarith
    have h2 : (y - 2020: ℝ) ^ 2 - 4 * (y: ℝ) * (y: ℝ) ≥ 0 := by
      have h7 : (y * (x ^ 2) + (y - 2020) * x + y) = 0 := eq2
      nlinarith [sq_nonneg (y * x + (y - 2020) / 2), sq_nonneg (x + (2020 - y) / (2 * y)), sq_nonneg (x + (y - 2020) / 2), sq_nonneg ((y) * x + (y - 2020) / 2), sq_nonneg ((y) * x - (y - 2020) / 2), sq_nonneg (x + (y - 2020)/ (2 * y)), sq_nonneg (y), sq_nonneg (y - 2020/3)]
    constructor
    · -- Show that -2020 ≤ y
      nlinarith
    · -- Show that y ≤ 2020 / 3
      nlinarith
  · -- Assume -2020 ≤ y ≤ 2020/3, prove y ∈ range f
    rintro ⟨hy1, hy2⟩
    by_cases h7 : y = 0
    · 
      use 0
      rw [h7]
      norm_num
    · 
      have h2 : y ≠ 0 := by intro h3; apply h7; linarith
      have h8 : (y - 2020) ^ 2 - 4 * y * y ≥ 0 := by
        nlinarith
      have h9 : ∃ x : ℝ, y * x ^ 2 + (y - 2020) * x + y = 0 := by
        use ( - (y - 2020) + Real.sqrt ((y - 2020) ^ 2 - 4 * y * y) ) / (2 * y)
        field_simp [h2]
        ring_nf
        rw [Real.sq_sqrt (by nlinarith)]
        <;> nlinarith
      rcases h9 with ⟨x, hx⟩
      use x
      have h11 : x ^ 2 + x + 1 > 0 := by
        nlinarith [sq_nonneg (x + 1 / 2)]
      have eq1 : 2020 * x = y * (x ^ 2 + x + 1) := by
        have eq2 : y * x ^ 2 + (y - 2020) * x + y = 0 := by
          nlinarith
        nlinarith
      have hne : x ^ 2 + x + 1 ≠ 0 := by
        nlinarith [sq_nonneg (x + 1 / 2)]
      field_simp [hne]
      linarith