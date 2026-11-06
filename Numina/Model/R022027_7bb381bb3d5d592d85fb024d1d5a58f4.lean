import Mathlib

theorem inequalities_234290 :
    Set.ncard {x : ℤ | x^4 - 2020 * x^2 + 2019 < 0} = 86 := by
  have h1 : {x : ℤ | x^4 - 2020 * x^2 + 2019 < 0} = Finset.filter (fun x : ℤ => x^4 - 2020 * x^2 + 2019 < 0) (Finset.Icc (-44 : ℤ) 44) := by 
    ext x 
    simp
    intro h 
    have h2 : x ≤ 44 := by 
      nlinarith [sq_nonneg (x ^ 2 - 2019), sq_nonneg (x + 44), sq_nonneg (x - 44), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 - 44^2), sq_nonneg (x)]
    have h3 : x ≥ -44 := by 
      nlinarith [sq_nonneg (x ^ 2 - 2019), sq_nonneg (x + 44), sq_nonneg (x - 44), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 - 44^2), sq_nonneg (x)]
    omega 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide