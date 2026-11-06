import Mathlib

theorem number_theory_369 (x y z : ℕ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0)
    (h : x*900+y*745+z*1385=260*10+370*10-5*(x+y+z)) :
    x=14 ∧ y=10 ∧ z=2 ∧ (x+y+z)=44 := by 
  have h1 : x * 905 + y * 750 + z * 1390 = 6300 := by
    omega
  have h2 : x ≤ 7 := by
    omega
  have h3 : y ≤ 8 := by
    omega
  have h4 : z ≤ 4 := by
    omega
  interval_cases x <;> interval_cases y <;> interval_cases z
    <;> omega