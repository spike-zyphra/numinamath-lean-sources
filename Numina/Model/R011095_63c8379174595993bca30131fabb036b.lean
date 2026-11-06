import Mathlib

theorem algebra_94725 (d t1 t2 : ℝ) (ht1 : t1 = 30 / 60) (ht2 : t2 = 10 / 60)
(hd : d = 1) :
(2 * d) / (t1 + t2) = 3 := by
  rw [ht1, ht2, hd]
  -- The goal becomes $2 \cdot 1 / (30/60 + 10/60) = 3$, which is $2 / (2/3) = 3$, i.e., $2 \cdot (3/2) = 3$.
  norm_num