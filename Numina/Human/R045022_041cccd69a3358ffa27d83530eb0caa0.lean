import Mathlib

/- Ellen baked $2$ dozen cupcakes of which half contained chocolate, two-thirds contained raisins, one-fourth contained chocolate chips, and one-sixth contained nuts.  What is the largest possible number of cupcakes that had none of these ingredients? -/
theorem algebra_20563 (total chocolate raisin chip nut : ℕ) (h1 : total = 2 * 12) (h2 : chocolate = total / 2) (h3 : raisin = 2 * total / 3) (h4 : chip = total / 4) (h5 : nut = total / 6) : IsGreatest {noingredient : ℕ | noingredient ≤ total - chocolate ∧ noingredient ≤ total - raisin ∧ noingredient ≤ total - chip ∧ noingredient ≤ total - nut} 8 := by
  simp only [h1, Nat.reduceMul, h2, Nat.reduceDiv, Nat.reduceSub, h3, h4, h5]
  constructor
  -- $8$ is a possible value
  simp only [Set.mem_setOf_eq, Nat.reduceLeDiff, le_refl, and_self]
  -- $8$ is the largest such value
  intro n nin
  simp at nin
  linarith