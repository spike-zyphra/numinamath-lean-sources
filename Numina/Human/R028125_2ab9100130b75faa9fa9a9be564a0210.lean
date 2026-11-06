import Mathlib

/- Given the following system of equations:
$$\begin{cases} R I +G +SP = 50 \\  R I +T + M = 63 \\ G +T +SP = 25 \\  SP + M = 13 \\   M +R I = 48 \\ N = 1 \end{cases}$$ 
Find the value of L that makes $LMT +SPR I NG = 2023$ true. 

 -/
theorem algebra_35535 {R I G T M S P N L : ℝ}
    (hR : R * I + G + S * P = 50) (hR' : R * I + T + M = 63)
    (hG : G + T + S * P = 25) (hSP : S * P + M = 13) (hM : M + R * I = 48)
    (hN : N = 1) :
    L * M * T + S * P * R * I * N * G = 2023 ↔ L = 341 / 40 := by
  -- subtract the fourth equation from the second.
  have eq_aux1 : R * I + T - S * P = 50 := by nlinarith
  -- use the equation above and the first equation.
  have eq_aux2 : T = G + 2 * S * P := by 
    nlinarith
  have eq_aux3 : M = 48 - R * I := by nlinarith
  -- substitude M = 48 - R * I into the fourth equation.
  have eq_aux4 : S * P = R * I - 35 := by nlinarith
  -- substitude S * P = R * I - 35 into the first equation.
  have eq_aux5 : R * I + G + (R * I - 35) = 50 := by nlinarith
  -- after simplify we get 
  have eq_aux6 : G = 85 - 2 * R * I := by nlinarith 
  have eq_aux7 : T = 85 - 2 * R * I + 2 * (R * I - 35) := by nlinarith
  have eq_aux8 : T = R * I - 25 := by nlinarith
  -- substitude what we get now to the third equation.
  have eq1 : R * I = 40 := by nlinarith
  have eq2 : M = 8 := by nlinarith
  have eq3 : S * P = 5 := by nlinarith
  have eq4 : G = 5 := by nlinarith
  have eq5 : T = 15 := by nlinarith
  simp [eq1,eq2,eq3,eq4, hN, eq5]
  constructor
  · intro h
    have this : L * 8 * 15 + 5 * (R * I) * 5 = 2023 := by 
      rw [←h]
      ring
    rw [eq1] at this
    nlinarith
  · intro h
    have this : L * 8 * 15 + 5 * (R * I) * 5 = 2023 := by 
      rw [h, eq1]
      ring
    rw [← this]
    ring
