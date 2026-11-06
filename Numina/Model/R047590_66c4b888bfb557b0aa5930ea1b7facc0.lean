import Mathlib


open Real



theorem algebra_297777 {f : ℝ → ℝ}
    (hf : ∀ x > 0, f x = ((x + 1 / x)^4 - (x^4 + 1 / x^4)) / ((x + 1 / x)^3 - (x^3 + 1 / x^3))) :
    IsLeast (Set.image f (Set.Ioi 0)) (7 / 3) := by
  have h1 : ∀ x > 0, f x = ((x + 1 / x) ^ 4 - (x ^ 4 + 1 / x ^ 4)) / ((x + 1 / x) ^ 3 - (x ^ 3 + 1 / x ^ 3)) := hf
  have h2 : ∀ x > 0, f x = (4 * (x + 1 / x) ^ 2 - 2) / (3 * (x + 1 / x)) := by
    intro x hx
    have h3 : (x + 1 / x) ^ 4 - (x ^ 4 + 1 / x ^ 4) = 4 * (x + 1 / x) ^ 2 - 2 := by
      field_simp
      ring
      -- linarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 - 1)]
      -- nlinarith
    have h4 : (x + 1 / x) ^ 3 - (x ^ 3 + 1 / x ^ 3) = 3 * (x + 1 / x) := by
      field_simp
      ring
    rw [h1 x hx, h3, h4]
    <;> ring
    all_goals linarith
  -- We need to show that 7/3 is the least of the image set.
  have h3 : ∀ x > 0, f x ≥ 7 / 3 := by
    intro x hx
    have h4 : f x = (4 * (x + 1 / x) ^ 2 - 2) / (3 * (x + 1 / x)) := h2 x hx
    rw [h4]
    have h5 : x + 1 / x ≥ 2 := by
      have h6 : x + 1 / x - 2 ≥ 0 := by
        have h7 : x + 1 / x - 2 = (x ^ 2 + 1 - 2 * x) / x := by
          field_simp
          ring
        rw [h7]
        have h8 : x ^ 2 + 1 - 2 * x ≥ 0 := by
          nlinarith [sq_nonneg (x - 1)]
        apply div_nonneg
        all_goals nlinarith
      linarith
    have hx1 : 3 * (x + 1 / x) > 0 := by
      positivity
    have h9 : 4 * (x + 1 / x) ^ 2 - 2 ≥ 7 * (x + 1 / x) := by
      nlinarith [sq_nonneg ((x + 1 / x) - 2)]
    apply (le_div_iff₀ hx1).mpr
    nlinarith
  have h5 : 7 / 3 ∈ Set.image f (Set.Ioi 0) := by
    use 1
    constructor
    norm_num
    -- Show f 1 = 7/3
    have h5 : f 1 = 7 / 3 := by
      rw [h1 1 (by norm_num)]
      norm_num
    linarith [h5]
  constructor
  exact h5
  intro y hy
  rcases hy with ⟨x, hx1, hfx⟩
  have hx2 : x > 0 := hx1
  -- Therefore, using the previous result
  have h4 : f x ≥ 7 / 3 := h3 x hx2
  linarith [hfx, h4]
  all_goals linarith