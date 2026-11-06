import Mathlib

/- An Internet service provider allows a certain number of free hours each month and then charges for each additional hour used. Wells, Ted, and Vino each have separate accounts. This month the total hours used by Wells and Ted was 105, and each used all of their free hours. Their total cost was $\$10$. Vino used 105 hours by himself and had to pay $\$26$. What is the number of cents charged for each extra hour? -/
theorem algebra_18657 (extra_hours_cost free_hours Wells_extra_hours Ted_extra_hours Vino_extra_hours : ℝ) (h₀ : 0 < extra_hours_cost ∧ 0 < free_hours ∧ 0 < Wells_extra_hours ∧ 0 < Ted_extra_hours ∧ 0 < Vino_extra_hours) (h₁ : (free_hours + Wells_extra_hours) + (free_hours + Ted_extra_hours) = 105) (h₂ : Wells_extra_hours * extra_hours_cost + Ted_extra_hours * extra_hours_cost = 10) (h₃ : free_hours + Vino_extra_hours = 105) (h₄ : Vino_extra_hours * extra_hours_cost = 26) :
    extra_hours_cost * 100 = 40 := by nlinarith
