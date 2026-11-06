import Mathlib

/-Josh and Mike live 13 miles apart. Yesterday Josh started to ride his bicycle toward Mike's house. A little later Mike started to ride his bicycle toward Josh's house. When they met, Josh had ridden for twice the length of time as Mike and at four-fifths of Mike's rate. How many miles had  Mike ridden when they met?-/
theorem algebra_19848 (d : ℝ) (h : d = 13) (josh_time mike_time josh_rate mike_rate : ℝ)(h1 : josh_time = 2 * mike_time) (h2 : josh_rate = (4 / 5) * mike_rate) (h3 : josh_time * josh_rate + mike_time * mike_rate = d) :
  mike_time * mike_rate = 5 := by
    -- Because $\text{(rate)(time)} = \text{(distance)}$, the distance Josh rode was $(4/5)(2) = 8/5$ of the distance that Mike rode.  Let $m$ be the number of miles that Mike had ridden when they met. Then the number of miles between their houses is \[
    -- 13 = m + \frac{8}{5}m = \frac{13}{5}m.
    -- \]Thus $m = \boxed{5}$.
    norm_num [h, h1, h2] at h3
    linarith