import Mathlib

/- If $|x-2|=p$, where $x<2$, then what is $x-p$ in terms of $p$? -/
theorem algebra_10897 {x p : ℝ} (hx : x < 2) (hxp : abs (x - 2) = p) :
    x - p = 2 - 2 * p := by 
  rw [abs_of_neg (sub_neg.mpr hx)] at hxp
  linarith