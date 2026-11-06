import Mathlib

/- A rectangular box has a volume of $4320$ cubic inches and a surface area of $1704$ square inches. The sum of the lengths of its $12$ edges is $208$ inches. What would be the volume of the box, in cubic inches, if its length, width and height were each increased by one inch? -/
theorem algebra_11587 {l w h : ℝ} (hl : l > 0) (hw : w > 0) (hw : h > 0)
    (hvol : l * w * h = 4320) (hsurf : 2 * (l * w + w * h + l * h) = 1704)
    (hedge : 4 * (l + w + h) = 208) :
    (l + 1) * (w + 1) * (h + 1) = 5225 := by
  have h₀ : l * w + w * h + l * h = 852 := by
    linarith
  have h₁ : l + w + h = 52 := by
    linarith
  linarith