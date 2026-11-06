import Mathlib

theorem number_theory_173293 (n : ℤ) (h : n^3 = 42 - 80435758145817515^3 - 12602123297335631^3) :
    n = -80538738812075974 := by
  have h1 : n^3 = (-80538738812075974 : ℤ) ^ 3 := by
    norm_num [h]
  have h999 : (n - (-80538738812075974 : ℤ)) * (n^2 + n * (-80538738812075974 : ℤ) + (-80538738812075974 : ℤ) ^ 2) = 0 := by 
    nlinarith [sq_nonneg (n + 80538738812075974 : ℤ), sq_nonneg (n - 80538738812075974 : ℤ), sq_nonneg (n : ℤ)]
  cases' (mul_eq_zero.mp h999) with h10 h11
  · -- Case where n - (-80538738812075974) = 0, which means n = -80538738812075974
    linarith
  · -- Case where the quadratic expression equals zero
    have h12 : n^2 + n * (-80538738812075974 : ℤ) + (-80538738812075974 : ℤ) ^ 2 = 0 := by 
      nlinarith
    nlinarith [sq_nonneg (n + 80538738812075974 : ℤ), sq_nonneg (n - 80538738812075974 : ℤ), sq_nonneg (n : ℤ)]