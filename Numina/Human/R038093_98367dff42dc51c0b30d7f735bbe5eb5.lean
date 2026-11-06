import Mathlib

/- Find the last two digits of $\tbinom{200}{100}$. Express the answer as an integer between $0$ and $99$. (e.g. if the last two digits are $05$, just write $5$.) -/
theorem number_theory_60859 : (Nat.choose 200 100) % 100 = 20 := by native_decide