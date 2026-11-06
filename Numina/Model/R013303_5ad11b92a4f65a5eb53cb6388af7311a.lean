import Mathlib

theorem algebra_288048 (f : ℝ → ℝ) (hf : f = fun x => (x - 16) * (x - 14) * (x + 14) * (x + 16)) :
    IsLeast (Set.image f (Set.univ : Set ℝ)) (-900) := by
  have h1 : ∀ x, f x = ((x) ^ 2 - 256) * ((x) ^ 2 - 196) := by
    intro x
    rw [hf]
    ring_nf

  have h2 : -900 ∈ Set.image f (Set.univ : Set ℝ) := by
    use Real.sqrt 226
    rw [h1]
    have h3 : (Real.sqrt 226 : ℝ) ^ 2 = (226 : ℝ) := Real.sq_sqrt (by norm_num)
    rw [h3]
    norm_num

  have h3 : ∀ y, y ∈ Set.image f (Set.univ : Set ℝ) → -900 ≤ y := by
    intros y hy
    rcases hy with ⟨x, hx⟩
    rw [h1] at hx
    nlinarith [sq_nonneg (x ^ 2 - 226), sq_nonneg (x ^ 2 - 226), sq_nonneg (x ^ 2 - 226), sq_nonneg (x ^ 2), sq_nonneg (x ^ 2 - 256), sq_nonneg (x ^ 2 - 196)]

  constructor
  · exact h2
  · intro y hy
    have h4 : y ∈ Set.image f (Set.univ : Set ℝ) := by
      simpa using hy
    have h5 : -900 ≤ y := h3 y h4
    linarith