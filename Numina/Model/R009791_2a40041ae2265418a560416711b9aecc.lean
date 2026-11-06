import Mathlib

theorem algebra_10676 (f g : ℝ → ℝ)
    (hf : f = fun x => 2 * x ^ 2 - 7 * x + 1)
    (hg : g = fun x => 8 * x ^ 2 + 5 * x + 1) :
    {(x, y) | y = f x ∧ y = g x} = {(-2, 23), (0, 1)} := by
  ext ⟨x, y⟩
  simp [hf, hg]
  constructor
  · -- Forward direction: if (x, y) is in the intersection, then (x, y) ∈ {(-2, 23), (0, 1)}
    rintro ⟨hy1, hy2⟩
    have h_eq : 2 * x ^ 2 - 7 * x + 1 = 8 * x ^ 2 + 5 * x + 1 := by
      linarith
    have h_quad : 6 * x ^ 2 + 12 * x = 0 := by
      linarith [h_eq]
    have h_factor : 6 * x * (x + 2) = 0 := by
      linarith [h_quad]
    cases' (mul_eq_zero.mp h_factor) with h1 h2
    · -- Case where 6 x = 0
      have hx : x = 0 := by
        linarith
      have hy : y = 1 := by
        rw [hx] at hy1
        linarith
      right
      exact ⟨hx, hy⟩
    · -- Case where x + 2 = 0
      have hx : x = -2 := by
        linarith
      have hy : y = 23 := by
        rw [hx] at hy1
        linarith
      left
      exact ⟨hx, hy⟩
  · -- Backward direction: if (x, y) ∈ {(-2, 23), (0, 1)}, then (x, y) is in the intersection
    rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · -- Case where (-2, 23)
      rw [hx, hy]
      constructor <;> norm_num
    · -- Case where (0, 1)
      rw [hx, hy]
      constructor <;> norm_num