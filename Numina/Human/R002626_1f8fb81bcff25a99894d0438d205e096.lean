import Mathlib.Tactic

/--
A college student drove his compact car $120$ miles home for the weekend and averaged $30$ miles per gallon. On the
return trip the student drove his parents' SUV and averaged only $20$ miles per gallon. What was the average gas
mileage, in miles per gallon, for the round trip?
$\textbf{(A) } 22 \qquad\textbf{(B) } 24 \qquad\textbf{(C) } 25 \qquad\textbf{(D) } 26 \qquad\textbf{(E) } 28$
-/
theorem alg_1184
    (d cc suv avg to_ga : ℚ)
    (distance : d = 120)
    (compact_car_mileage : cc = 30)
    (suv_mileage : suv = 20)
    (total_gallon : to_ga = d / cc + d / suv)
    (avg_mileage : avg = (2 * d) / to_ga) :
    avg = 24 := by

  -- First calculate the total gallon used.
  rw [distance, compact_car_mileage, suv_mileage] at total_gallon
  norm_num at total_gallon

  -- Then, calculate the average mileage.
  rw [distance, total_gallon] at avg_mileage
  norm_num at avg_mileage
  exact avg_mileage