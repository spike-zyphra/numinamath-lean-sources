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
  · -- First prove 2 belongs to the set
    use -1, 0
    norm_num [abs_of_nonneg, Real.cos_zero, Real.sin_zero]
    all_goals norm_num

  · -- Then prove it's the minimum
    intro x hx
    rcases hx with ⟨s, t, heq⟩
    have h1 : 0 ≤ abs (cos t) := abs_nonneg (cos t)
    have h2 : 0 ≤ abs (sin t) := abs_nonneg (sin t)
    have h3 : abs (cos t) ^ 2 + abs (sin t) ^ 2 ≤ 1 := by
      have h1 : abs (cos t) ^ 2 + abs (sin t) ^ 2 = Real.cos t ^ 2 + Real.sin t ^ 2 := by
        simp [abs_pow]
      have h4 : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := Real.cos_sq_add_sin_sq t
      linarith [h1, h4]

    have h5 : (s + 5 - 3 * abs (cos t))^2 + (s - 2 * abs (sin t))^2 ≥ 2 := by
      nlinarith [sq_nonneg (s + 1), sq_nonneg (abs (cos t) - 1), sq_nonneg (abs (sin t) - 0), 
        abs_nonneg (cos t), abs_nonneg (sin t), 
        Real.cos_sq_add_sin_sq t, 
        abs_le.mp (show abs (cos t) ≤ 1 by apply abs_le.2 (by constructor <;> nlinarith [Real.cos_sq_add_sin_sq t])),
        abs_le.mp (show abs (sin t) ≤ 1 by apply abs_le.2 (by constructor <;> nlinarith [Real.cos_sq_add_sin_sq t]))]
    linarith [heq, h5]