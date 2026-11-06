import Mathlib

/- ## Task B-1.6.

Luka and Pero decided to visit a friend and set off from place $A$ to place $B$, which is $170 \mathrm{~km}$ away. Luka started walking, while Pero was driven by a motorcyclist. After some time, the motorcyclist returned to pick up Luka, and Pero continued on foot, so that both arrived at place $B$ at the same time. Both pedestrians walk at the same speed of $5 \mathrm{~km} / \mathrm{h}$, and the motorcyclist drives at a speed of $85 \mathrm{~km} / \mathrm{h}$. At what distance from place $B$ and after how much time did the motorcyclist stop and return to pick up Luka? How long did it take for Luka and Pero to travel from place $A$ to place $B$? -/
theorem algebra_232003 {s t x : ℝ} (hs : s = 170) (h1 : x / 5 = (2 * s - 3 * x) / 85) (h2 : t = x / 5 + (s - x) / 85) :
    x = 17 ∧ t = 26/5 := by
  -- substitute in and conclude
  constructor <;> linarith