import Mathlib

theorem algebra_274997 (total_savings : ℝ) (h : total_savings ≠ 0)
    (x_investment y_investment z_investment : ℝ)
    (hx_investment : x_investment = total_savings * (1 / 5))
    (hy_investment : y_investment = total_savings * (42 / 100))
    (hz_investment : z_investment = total_savings - x_investment - y_investment)
    (hy_investment_eq : y_investment = 10500) :
    z_investment = 9500 := by
  have eq1 : total_savings * (42 / 100) = 10500 := by
    linarith [hy_investment, hy_investment_eq]
  have total_savings_eq : total_savings = 25000 := by
    linarith
  have h1 : x_investment = 5000 := by
    rw [hx_investment]
    rw [total_savings_eq]
    linarith
  have h2 : z_investment = 9500 := by
    rw [hz_investment]
    rw [total_savings_eq, h1, hy_investment_eq]
    linarith
  linarith [h2]