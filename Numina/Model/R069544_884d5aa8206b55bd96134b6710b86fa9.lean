import Mathlib

/- The root of the equation $5x+4=16k-x$ with respect to $x$ is greater than $2002$ and less than $2018$, the range of values for $k$ is ___          ___. -/
theorem algebra_4659 (k : ℝ) (h : ∃ x, 5 * x + 4 = 16 * k - x ∧ x > 2002 ∧ x < 2018) :
    757 > k ∧ k > 751 := by
  rcases h with ⟨x, hk_eq, hx1, hx2⟩
  have hx_eq : x = (16 * k - 4) / 6 := by
    linarith 
  have h1 : (16 * k - 4) / 6 > 2002 := by 
    linarith [hx_eq, hx1] 
  have h2 : (16 * k - 4) / 6 < 2018 := by 
    linarith [hx_eq, hx2] 
  have hk1 : k > 751 := by 
    linarith 
  have hk2 : k < 757 := by
    linarith 
  constructor 
  · linarith 
  · linarith