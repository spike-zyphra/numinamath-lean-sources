import Mathlib

/- Find the remainder when $$\left \lfloor \frac{149^{151} + 151^{149}}{22499}\right \rfloor$$ is divided by $10^4$.

[i]Proposed by Vijay Srinivasan[/i] -/
theorem number_theory_65005 : ((149^151 + 151^149) / 22499) % 10000 = 7800 := by
  rfl
