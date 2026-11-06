import Mathlib

theorem number_theory (a b x y z:ℕ) (ha: 0 < a) (hx: 0 < x) (au : a ≤ 9) (bu: b ≤ 9) (xu: x ≤ 9) (yu: y ≤ 9) (zu: z ≤ 9)  (hxyz: x < y ∧ y < z):
((10*a+b)*(x^2+y^2+z^2)=(1*2*19*53)) 
↔ 
(a=1∧b=9∧x=3∧y=4∧z=9) ∨ (a=3∧b=8∧x=1∧y=4∧z=6) ∨ (a=5∧b=3∧x=2∧y=3∧z=5) := by
  constructor
  · -- Forward direction: given the equation, prove one of the three cases must hold
    intro h
    have eq : (10*a + b) * (x^2 + y^2 + z^2) = 2014 := by
      norm_num at h
      omega
    have h1 : a ≤ 9 := by omega
    have h2 : b ≤ 9 := by omega
    have h3 : x ≤ 9 := by omega
    have h4 : y ≤ 9 := by omega
    have h5 : z ≤ 9 := by omega
    -- Now use an exhaustive search over all possible values of the variables within their bounds
    have h6 : a ≥ 1 := by omega
    have h7 : x ≥ 1 := by omega
    interval_cases a <;> try { omega } <;> interval_cases b 
    <;> try { omega }
    <;> interval_cases x <;> try { omega }
    <;> interval_cases y <;> try { omega } <;> interval_cases z <;> omega
  · -- Backward direction: given one of the cases, prove the equation 
    rintro (h | h | h)
    · -- First case
      rcases h with ⟨ha1, hb1, hx1, hy1, hz1⟩
      norm_num [ha1, hb1, hx1, hy1, hz1]
    · -- Second case
      rcases h with ⟨ha1, hb1, hx1, hy1, hz1⟩
      norm_num [ha1, hb1, hx1, hy1, hz1]
    · -- Third case
      rcases h with ⟨ha1, hb1, hx1, hy1, hz1⟩
      norm_num [ha1, hb1, hx1, hy1, hz1]