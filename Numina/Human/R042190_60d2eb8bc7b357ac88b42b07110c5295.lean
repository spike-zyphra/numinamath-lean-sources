import Mathlib

/- I am going to buy exotic fruits.  Dragonfruit costs $x-4$ dollars.  Starfruit is five dollars less expensive than rambutan.  Rambutan costs $2x$ dollars more than dragonfruit.  How much does it cost to buy one rambutan, two starfruit, and three dragonfruit? Your answer will be an expression that depends on $x$. -/
theorem algebra_18686 (x dragonfruit starfruit rambutan: ℝ) (h₀ : 0 < x) (h₁ : dragonfruit = x - 4) (h₂ : starfruit = rambutan - 5) (h₃ : rambutan = dragonfruit + 2 * x) :
  1 * rambutan + 2 * starfruit + 3 * dragonfruit = 12 * x - 34 := by
  linarith