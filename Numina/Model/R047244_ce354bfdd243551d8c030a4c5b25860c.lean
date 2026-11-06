import Mathlib
open Set

theorem algebra_9046 (S : Set (ℝ × ℝ × ℝ)) (hS : S = {(x, y, z) | 0 < x ∧ 0 < y ∧ 0 < z ∧ x^2 - 3 * x * y + 4 * y^2 - z = 0}) : IsGreatest (image (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ x + 2 * y - z) {(x, y, z) | (x, y, z) ∈ S ∧ IsLeast (image (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ z / (x * y)) S) (z / (x * y))}) 2 := by
  constructor
  · -- Show that 2 is in the image.
    use (2, 1, 2)
    constructor
    · -- Show that (2, 1, 2) ∈ S ∧ IsLeast (image (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ z / (x * y)) S) (z / (x * y))
      constructor
      · -- Show that (2, 1, 2) ∈ S
        rw [hS]
        exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
      · -- Show that (2, 1, 2) minimizes z / (x * y)
        rw [hS]
        constructor
        · -- Show that z / (x * y) is in the image.
          use (2, 1, 2)
          norm_num
          <;> norm_num
        · -- Show that for all w in the image set, w ≥ z / (2 * 1)
          intro w hw
          rcases hw with ⟨p, hp, h_eq⟩
          simp [Prod.ext_iff] at hp h_eq
          rcases p with ⟨x, y, z⟩
          rcases hp with ⟨hx1, hy1, hz1, h_eq1⟩
          have h1 : z / (x * y) ≥ (1 : ℝ) := by
            have h2 : z = x^2 - 3 * x * y + 4 * y^2 := by linarith
            rw [h2]
            have h3 : x^2 - 3 * x * y + 4 * y^2 ≥ x * y := by
              nlinarith [sq_nonneg (x - 2 * y), sq_nonneg (y), sq_nonneg (x - 2), sq_nonneg (y - 1)]
            have h4 : x * y > 0 := mul_pos hx1 hy1
            apply (le_div_iff₀ h4).mpr
            nlinarith
          linarith [h1, h_eq]
    · -- Show that 2 is obtained through the function application.
      norm_num
  · -- Show that 2 is indeed the greatest.
    intro a ha
    rcases ha with ⟨p, hp, ha⟩
    simp at hp ha
    rcases p with ⟨x, y, z⟩
    rcases hp with ⟨hp1, hp2⟩
    rw [hS] at hp1
    rcases hp1 with ⟨hx1, hy1, hz1, h_eq1⟩
    have h1 : z / (x * y) ≥ (1 : ℝ) := by
      have h2 : z = x^2 - 3 * x * y + 4 * y^2 := by linarith
      rw [h2]
      have h3 : x^2 - 3 * x * y + 4 * y^2 ≥ x * y := by
        nlinarith [sq_nonneg (x - 2 * y), sq_nonneg (y), sq_nonneg (x - 2), sq_nonneg (y - 1), sq_nonneg (x * y - 1)]
      have h4 : x * y > 0 := mul_pos hx1 hy1
      apply (le_div_iff₀ h4).mpr
      nlinarith
    have h2 : x + 2 * y - z ≤ (2 : ℝ) := by
      have h2 : z = x^2 - 3 * x * y + 4 * y^2 := by linarith
      rw [h2] at *
      nlinarith [sq_nonneg (x - 2 * y), sq_nonneg (y ^ 2 - 1), sq_nonneg (x - 2), sq_nonneg (y - 1), sq_nonneg ((x * y) - 2), mul_pos hx1 hy1, sq_nonneg (z - 2)]
    linarith [h2, ha]