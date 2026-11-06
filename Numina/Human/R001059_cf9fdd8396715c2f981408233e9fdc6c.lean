import Mathlib

/- A rectangular garden has a length that is twice its width. The dimensions are increased so that the perimeter is doubled and the new shape is a square with an area of 3600 square feet. What was the area of the original garden, in square feet? -/
theorem algebra_20243 {l w nw: ℝ} (hl : l = 2 * w) (hperim : 2 * 2 * (l + w) = 4 * nw) (harea : nw^2 = 3600) :
    l * w = 800 := by

  -- Let $w$ be the width of the original rectangular garden.  The perimeter of the rectangle is $2(w+2w)=6w$, so the perimeter of the square is $12w$. The dimensions of the square are $3w\times 3w$ and its area is $(3w)(3w)=9w^2$
  have hnw : nw = 3 * w := by
    rw [hl, show 2 * w + w = 3 * w by ring] at hperim
    --rw [show (2:ℝ) * 2 = 4 by ring] at hperim
    apply_fun fun t => t / 4 at hperim
    norm_num at hperim
    exact hperim.symm

  -- so set $9w^2=3600\text{ ft.}^2$ to find $w^2=400$ square feet.
  have hwsq : w ^ 2 = 400 := by
    rw [hnw] at harea
    linarith

  -- The area of the original rectangle is $(2w)(w)=2w^2=2\cdot400\text{ ft.}^2=\boxed{800}$ square feet.
  rw [hl, mul_assoc, ← pow_two, hwsq]
  norm_num
