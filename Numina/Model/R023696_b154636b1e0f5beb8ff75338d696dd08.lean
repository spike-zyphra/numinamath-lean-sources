import Mathlib

theorem algebra_149231 {P : Polynomial ℤ} (hP1 : P.eval 19 = 1994) (hP2 : P.eval 94 = 1994)
    (hP3 : |P.eval 0| < 1000) :
    P.eval 0 = 208 := by
  have h1 : (19 : ℤ) ∣ P.eval 19 - P.eval 0 := by 
    apply P.sub_dvd_eval_sub
  have h2 : (94 : ℤ) ∣ P.eval 94 - P.eval 0 := by 
    apply P.sub_dvd_eval_sub
  rw [hP1] at h1
  rw [hP2] at h2
  have h19 : P.eval 0 % 19 = 18 := by
    omega
  have h94 : P.eval 0 % 94 = 20 := by
    omega
  have h5 : P.eval 0 % 1786 = 208 := by
    omega
  -- Show with hP3 yu can derive it
  have h6 : P.eval 0 = 208 := by
    have h7 : P.eval 0 % 1786 = 208 := h5
    have h8 : P.eval 0 > -1000 := by
      linarith [abs_lt.mp hP3]
    have h9 : P.eval 0 < 1000 := by
      linarith [abs_lt.mp hP3]
    -- Now show that it has to be 208
    omega
  exact h6