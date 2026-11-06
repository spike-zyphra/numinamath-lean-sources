import Mathlib

/-Let $M_{total}$ be the initial amount of money Grisha has, a non-negative integer.
Chocolate bunnies are sold at 45 rubles each. Bags are sold at 30 rubles each.
No more than 30 chocolate bunnies can fit in one bag. Grisha wants to buy the maximum possible number of bunnies, $b_{max}$.
Let $g_{max}$ be the number of bags Grisha needs to carry $b_{max}$ bunnies.
If $b_{max} = 0$, then $g_{max} = 0$. If $b_{max} > 0$, then $g_{max} = (b_{max} + 30 - 1) / 30$ using integer division.
The total cost must not exceed $M_{total}$. Determine the amount of money Grisha has left.
Show that if $M_{total}=4600$, the amount of money left is 25.-/

theorem number_theory_636357 (M_total b_max g_max: ℤ)
  (h1: M_total = 4600)
  (h2: g_max = (b_max + 30 - 1) / 30)
  (h3: IsGreatest {k: ℤ | 0 ≤ k ∧ 45 * k + 30 * ((k + 30 - 1) / 30) ≤ M_total} b_max):
  M_total - (45 * b_max + 30 * g_max) = 25 := by

  -- it suffices to show that b_max is 99
  suffices b_max = 99 by
    simp [this] at h2
    simp [h2, this, h1]

  suffices IsGreatest {k | 0 ≤ k ∧ 45 * k + 30 * ((k + 30 - 1) / 30) ≤ M_total} 99 by
    rw [IsGreatest.isGreatest_iff_eq h3] at this
    tauto

  constructor

  -- the forward direction
  .
    simp
    omega


  -- the backward direction
  .
    intro k h
    simp at h
    rcases h with ⟨f1, f2⟩
    rw [h1] at f2
    by_contra! l
    clear *- l f2
    omega