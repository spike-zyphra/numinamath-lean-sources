import Mathlib

/- Bekah has exactly three brass house number digits: 2, 3 and 5. How many distinct numbers can she form using one or more of the digits? -/
theorem algebra_20004 : ({2, 3, 5} : Finset ℕ).card + ({23, 25, 32, 35, 52, 53} : Finset ℕ).card + ({235, 253, 325, 352, 523, 532} : Finset ℕ).card = 15 := by
  exact rfl