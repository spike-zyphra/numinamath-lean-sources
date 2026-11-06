import Mathlib

/- If for the real numbers $x, y, z, k$ the following conditions are valid, $x \neq y \neq z \neq x$ and $x^{3}+y^{3}+k\left(x^{2}+y^{2}\right)=y^{3}+z^{3}+k\left(y^{2}+z^{2}\right)=z^{3}+x^{3}+k\left(z^{2}+x^{2}\right)=2008$, find the product $x y z$. -/
theorem algebra_604633 (x y z k : ℝ) (h₀ : x ≠ y) (h₁ : y ≠ z) (h₂ : z ≠ x) (h₃ : x ^ 3 + y ^ 3 + k * (x ^ 2 + y ^ 2) = y ^ 3 + z ^ 3 + k * (y ^ 2 + z ^ 2)) (h₄ : y ^ 3 + z ^ 3 + k * (y ^ 2 + z ^ 2) = z ^ 3 + x ^ 3 + k * (z ^ 2 + x ^ 2)) (h₅ : z ^ 3 + x ^ 3 + k * (z ^ 2 + x ^ 2) = 2008) : x * y * z = 1004 := by
  -- Show that x² + xz + z² = -k(x + z) from hypothesis h₃.
  have h₆ : x ^ 2 + x * z + z ^ 2 = -k * (x + z) := by
    -- Multiply both sides of the goal by x - z to become a rearrangement of terms from h₃.
    apply mul_right_cancel₀ (show x - z ≠ 0 by contrapose! h₂; linarith only [h₂])
    linarith only [h₃]
  -- Show that y² + yx + x² = -k(y + x) from hypothesis h₄.
  have h₇ : y ^ 2 + y * x + x ^ 2 = -k * (y + x) := by
    -- Multiply both sides of the goal by y - x to become a rearrangement of terms from h₄.
    apply mul_right_cancel₀ (show y - x ≠ 0 by contrapose! h₀; linarith only [h₀])
    linarith only [h₄]
  -- Show that x + y + z = -k by h₆ - h₇.
  have h₈ : x + y + z = -k := by
    -- Multiply both sides of the goal by z - y.
    apply mul_right_cancel₀ (show z - y ≠ 0 by contrapose! h₁; linarith only [h₁])
    linarith only [h₆, h₇]
  -- Show that x + z ≠ 0 by contradiction.
  have h₉ : x + z ≠ 0 := by
    -- Assume x + z = 0.
    intro h
    -- We have x * z = 0.
    replace h₆ : (x + z) ^ 2 - x * z = 0 := by
      rw [h] at h₆
      linarith only [h₆]
    simp [h] at h₆
    -- We derive a contradiction either for x = 0 or z = 0.
    cases h₆ with
    | inl h₆ =>
      contrapose! h₂
      linarith only [h, h₆, h₂]
    | inr h₆ =>
      contrapose! h₂
      linarith only [h, h₆, h₂]
  -- Show that  y + x ≠ 0 by contradiction.
  have h₁₀ :  y + x ≠ 0 := by
    -- Assume  y + x = 0.
    intro h
    -- We have x * y = 0.
    replace h₇ : ( y + x) ^ 2 - x * y = 0 := by
      rw [h] at h₇
      linarith only [h₇]
    simp [h] at h₇
    -- We derive a contradiction either for x = 0 or y = 0.
    cases h₇ with
    | inl h₇ =>
      contrapose! h₀
      linarith only [h, h₇, h₀]
    | inr h₇ =>
      contrapose! h₀
      linarith only [h, h₇, h₀]
  -- Show that -k = (x² + xz + z²) / (x + z) by subtracting both sides of h₆ by x + z.
  replace h₆ : -k = (x ^ 2 + x * z + z ^ 2) / (x + z) := by
    rw [div_eq_of_eq_mul h₉]
    linarith only [h₆]
  -- Show that xy + yz + zx = 0 by combining h₈ and h₆
  have h₁₁ := (h₈ ▸ h₆).symm
  rw [div_eq_iff h₉] at h₁₁
  replace h₁₁ : x * y + y * z + z * x = 0 := by
    linarith only [h₁₁]
  -- Show that x³ + y³ + k(x² + y²) = 2008 by combining h₃, h₄ and h₅.
  replace h₅ := h₃ ▸ h₄ ▸ h₅
  -- Substitute h₈ into h₅.
  rw [<-neg_eq_iff_eq_neg] at h₈
  rw [<-h₈] at h₅
  -- Multiply both sides of h₁₁ by  y + x.
  replace h₁₁ : (x * y + y * z + z * x) * ( y + x) = 0 := by
    simp [h₁₁]
  -- Show that xyz = 1004 by combining h₅ and h₁₁ to complete the proof.
  linarith only [h₅, h₁₁]
