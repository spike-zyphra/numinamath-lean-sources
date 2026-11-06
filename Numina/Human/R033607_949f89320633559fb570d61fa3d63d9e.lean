import Mathlib

/- A baker bakes a batch of muffins and splits the batch evenly onto six different trays.  She then adds five croissants to each tray. If each tray now contains at least twenty baked goods, what is the least possible number of muffins in the baker's original batch? -/
theorem algebra_19758 {n : ℕ} (hn : n % 6 = 0) (h : n / 6 + 5 ≥ 20) :
    n ≥ 90 := by 
  omega