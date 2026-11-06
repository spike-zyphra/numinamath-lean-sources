import Mathlib

/- Billy Goats invested some money in stocks and bonds. The total amount he invested was $\$165,\!000$. If he invested 4.5 times as much in stocks as he did in bonds, what was his total investment in stocks? -/
theorem algebra_17062 {x y : ℝ} (h : x + y = 165000) (h' : x = 4.5 * y) :
    x = 135000 := by
  norm_num at h h' ⊢
  nlinarith