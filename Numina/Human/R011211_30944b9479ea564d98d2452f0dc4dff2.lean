import Mathlib

open Real Set

/- 6. When $s$ and $t$ take all real values, the minimum value that $(s+5-3|\cos t|)^{2}+(s-2|\sin t|)^{2}$ can achieve is -/

-- write squared distance to (s + 5, s) as square of perpendicular distance + parallel distance, in paritcular (s + 5, s)'s perpendicular direction has x + y = constant equation
lemma l_perp_dist (a b s : ℝ) : (s + 5 - a) ^ 2 + (s - b) ^ 2 = (s + 5 - (a + b + 5)/2)^2 +
    (s - (a + b - 5)/2)^2 + (((a + b + 5)/2 - a)^2 + ((a + b - 5)/2 - b)^2) := by
  ring

-- the perpendicular distance is than lower bound for distance to (s + 5, s)
lemma l_min_perp_dist (a b s : ℝ) : ((a + b + 5)/2 - a)^2 + ((a + b - 5)/2 - b)^2 ≤
    (s + 5 - a) ^ 2 + (s - b) ^ 2 := by
  rw [l_perp_dist a b s]
  apply le_add_of_nonneg_left
  positivity

-- if a ≤ 3 and 0 ≤ b then perpendicular distance of (a, b) to (s + 5, s) is greater than 2, in particular both terms are greater than 1
lemma l_min_dist_of_le_le (a b : ℝ) (ha : a ≤ 3) (hb : 0 ≤ b) : 2 ≤ ((a + b + 5)/2 - a)^2 + ((a + b - 5)/2 - b)^2 := by
  convert_to 1 ^ 2 + 1 ^ 2 ≤ ((a + b + 5)/2 - a)^2 + (b - (a + b - 5)/2)^2
  . norm_num
  . ring
  gcongr
  . linarith
  . linarith

theorem algebra_115275 : IsLeast {x : ℝ | ∃ s t, x = (s + 5 - 3 * abs (cos t))^2 + (s - 2 * abs (sin t))^2} 2 := by
  constructor
  -- to show 2 is a value in the set, use -1 and 0
  . use -1, 0
    simp
    norm_num
  -- to show 2 is lower bound, use the lemma's and finally show 3 * |cos t| ≤ 3 and 0 ≤ 2 * |sin t|
  . rintro x ⟨s, t, hx⟩
    rw [hx]
    trans
    swap
    . apply l_min_perp_dist
    . apply l_min_dist_of_le_le
      . suffices |cos t| ≤ 1 by linarith
        rw [abs_le]
        exact ⟨neg_one_le_cos t, cos_le_one t⟩
      . positivity