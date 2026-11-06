import Mathlib

theorem algebra_20563 (total chocolate raisin chip nut : ℕ) (h1 : total = 2 * 12) (h2 : chocolate = total / 2) (h3 : raisin = 2 * total / 3) (h4 : chip = total / 4) (h5 : nut = total / 6) : IsGreatest {noingredient : ℕ | noingredient ≤ total - chocolate ∧ noingredient ≤ total - raisin ∧ noingredient ≤ total - chip ∧ noingredient ≤ total - nut} 8 := by 
  subst total
  subst chocolate
  subst raisin
  subst chip
  subst nut
  constructor
  · -- Show 8 is in the set
    show 8 ≤ 24 - 12 ∧ 8 ≤ 24 - 16 ∧ 8 ≤ 24 - 6 ∧ 8 ≤ 24 - 4
    all_goals
      omega
  · -- Show if noingredient is in the set, then noingredient ≤ 8
    intro noingredient
    intro h
    rcases h with ⟨h1, h2, h3, h4⟩
    omega