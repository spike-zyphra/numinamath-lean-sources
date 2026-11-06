import Mathlib


/- Kirsty needs to hire a plumber to fix her house. The plumber charges $242_5$ dollars for every hour of labor and $367_{8}$ dollars for equipment. If the plumber works for $3.5_{10}$ hours, how many dollars (in base ten) will Kirsty owe the plumber? -/
theorem number_theory_22685 {work_time price_labor price_equipment : ℝ}
  (hw: work_time = 3.5) (hl: price_labor = Nat.ofDigits 5 [2,4,2])
  (he: price_equipment = Nat.ofDigits 8 [7,6,3])
   : price_labor * work_time + price_equipment = 499 := by 
  have : price_labor = 72 := by rw [hl]; norm_cast
  rw [this, hw]
  have : price_equipment = 247 := by rw [he]; norm_cast
  rw [this]
  norm_num
