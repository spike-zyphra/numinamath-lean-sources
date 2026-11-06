import Mathlib

theorem algebra_5137 (f : ℝ → ℝ) (hf : f = fun x => 18 * x ^ 2 + 12 * x + 37) :
    IsLeast (Set.image f (Set.univ : Set ℝ)) 35 := by 
  have h1 : ∀ x : ℝ, f x = 18 * (x + 1/3) ^ 2 + 35 := by
    intro x
    rw [hf]
    ring_nf
  have h2 : 35 ∈ Set.image f (Set.univ : Set ℝ) := by
    use -1/3
    rw [h1]
    all_goals norm_num
  have h3 : ∀ (y : ℝ), y ∈ Set.image f (Set.univ : Set ℝ) → 35 ≤ y := by
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [h1] at hx
    have h4 : 18 * (x + 1/3) ^ 2 ≥ 0 := by
      apply mul_nonneg
      norm_num
      apply pow_two_nonneg
    linarith
  exact ⟨h2, h3⟩