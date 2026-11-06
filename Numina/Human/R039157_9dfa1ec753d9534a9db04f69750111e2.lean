import Mathlib

/- The ratio of the length of a rectangular room to its width is $5:3$. The perimeter of the room is 48 feet. What is the area of the room? -/
theorem algebra_19905 {l w : ℝ} (hw : w ≠ 0) (h₀ : l / w = 5 / 3) (h₁ : 2 * (l + w) = 48) :
    l * w = 135 := by
  have h₂ : l = 5 * w / 3 := by
    field_simp [hw] at h₀
    linarith
  rw [h₂] at h₁
  field_simp [hw] at h₁
  nlinarith