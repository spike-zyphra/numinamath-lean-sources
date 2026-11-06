import Mathlib

/-On Monday at work, David produces $w$ widgets per hour, and works for $t$ hours. Exhausted by this work, on Tuesday, he decides to work for $2$ fewer hours, but manages to produce $4$ additional widgets per hour. If $w = 2t$, how many more widgets did David produce on Monday than on Tuesday?-/
theorem algebra_13820 {w t : ℕ} (ht : w = 2 * t) :
    w * t - (w + 4) * (t - 2) = (8 : ℤ) := by
  -- On Monday, David produces $w\ \frac{\text{widgets}}{\text{hour}} \cdot t\ \text{hours} = wt\ \text{widgets}$.
  -- On Tuesday, David produces $(w+4)\ \frac{\text{widgets}}{\text{hour}} \cdot (t-2)\ \text{hours} = (w+4)(t-2)\ \text{widgets}$.
  -- Substituting $w = 2t$, the difference in output between Monday and Tuesday is  \begin{align*}wt - (w+4)(t-2) &= (2t)t - ((2t) + 4)(t-2) \\ &= 2t^2 - (2t^2 + 4t - 4t - 8) \\&= \boxed{8}
  -- \end{align*}widgets.
  rw [ht]
  ring_nf
  norm_num
  ring_nf
