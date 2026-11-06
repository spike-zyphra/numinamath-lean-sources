import Mathlib

/- Line $l$ has equation $y = 4x - 7$, and line $m$ with equation $y = ax + b$ is perpendicular to line $l$ at $(2,1)$. What is the $y$-coordinate of the point on $m$ that has $x$-coordinate 6? -/
theorem algebra_19399 (a b : ℝ) (ha : a * 4 = -1) (hb : 2 * a + b = 1) :
    6 * a + b = 0 := by
  -- $a = -1/4$
  have ha' : a = -1/4 := by
    field_simp
    exact ha
  -- $b = 3/2$
  have hb' : b = 3/2 := by
    rw [ha'] at hb
    ring_nf at hb
    rw [add_comm] at hb
    apply eq_sub_of_add_eq at hb
    norm_num at hb
    exact hb
  -- $y = 0$
  have hm : 6 * a + b = 0 := by
    rw [ha', hb']
    norm_num
  exact hm