import Mathlib

open Real

/- 76. Let $u, v, w$ be positive real numbers, satisfying the condition $u \sqrt{v w}+v \sqrt{w u}+w \sqrt{u v}=1$, find the minimum value of $u+v+$ $w$ ( (3rd China Girls Mathematical Olympiad problem) -/
theorem algebra_599504
    : IsLeast {S : ℝ | ∃ u v w : ℝ, (0 < u ∧ 0 < v ∧ 0 < w ∧ u * sqrt (v * w) + v * sqrt (w * u) + w * sqrt (u * v) = 1 ∧ S = u + v + w)} (sqrt 3):= by
  constructor
  -- First part: Prove that sqrt(3) belongs to the set
  .
    simp
    -- We use u = v = w = sqrt(3)/3 as our candidate solution
    use (√3 / 3)
    refine ⟨(by positivity), ?_⟩
    use (√3 / 3)
    refine ⟨(by positivity), ?_⟩
    use (√3 / 3)
    refine ⟨(by positivity), ?_⟩
    constructor
    all_goals
      ring_nf
    field_simp
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
    field_simp
  -- Second part: Prove that sqrt(3) is a lower bound for the set
  .
    simp [lowerBounds]
    intro S u hu v hv w hw h hS
    subst S
    -- Restate the constraint equation
    have h1 : u * sqrt (v * w) + v * sqrt (w * u) + w * sqrt (u * v) = 1 := h
    -- Rewrite using the property sqrt(a*b) = sqrt(a)*sqrt(b) for positive a,b
    have h2 : u * sqrt v * sqrt w + v * sqrt w * sqrt u + w * sqrt u * sqrt v = 1 := by
      have h2 : sqrt (v * w) = sqrt v * sqrt w := by
        rw [sqrt_mul (by linarith)]
      have h3 : sqrt (w * u) = sqrt w * sqrt u := by
        rw [sqrt_mul (by linarith)]
      have h4 : sqrt (u * v) = sqrt u * sqrt v := by
        rw [sqrt_mul (by linarith)]
      rw [h2, h3, h4] at h1
      linarith
    -- Apply AM-GM inequality to show that u*v + v*w + w*u ≥ 1
    have h3 : u * v + v * w + w * u ≥ 1 := by
      -- For each term, apply AM-GM inequality: sqrt(a)*sqrt(b) ≤ (a+b)/2
      have h4 : u * sqrt v * sqrt w ≤ u * (v + w) / 2 := by
        have h5 : sqrt v * sqrt w ≤ (v + w) / 2 := by
          have _ : (sqrt v - sqrt w) ^ 2 ≥ 0 := sq_nonneg (sqrt v - sqrt w)
          have h7 : sqrt v * sqrt w ≤ (v + w) / 2 := by
            have h8 : (sqrt v * sqrt w) ≤ (v + w) / 2 := by
              nlinarith [mul_self_nonneg (sqrt v * sqrt w),
                  Real.sq_sqrt (show 0 ≤ v by linarith [hv]), Real.sq_sqrt (show 0 ≤ w by linarith [hw])]
            linarith
          linarith
        nlinarith [mul_nonneg (by linarith : 0 ≤ u) (by linarith : 0 ≤ (v + w) / 2),
            h5]
      have h5 : v * sqrt w * sqrt u ≤ v * (w + u) / 2 := by
        have h6 : sqrt w * sqrt u ≤ (w + u) / 2 := by
          have _ : (sqrt w - sqrt u) ^ 2 ≥ 0 := sq_nonneg (sqrt w - sqrt u)
          have h8 : sqrt w * sqrt u ≤ (w + u) / 2 := by
            nlinarith [mul_self_nonneg (sqrt w * sqrt u),
                  Real.sq_sqrt (show 0 ≤ w by linarith [hw]), Real.sq_sqrt (show 0 ≤ u by linarith [hu])]
          linarith
        nlinarith [mul_nonneg (by linarith : 0 ≤ v) (by linarith : 0 ≤ (w + u) / 2),
            h6]
      have h7 : w * sqrt u * sqrt v ≤ w * (u + v) / 2 := by
        have h8 : sqrt u * sqrt v ≤ (u + v) / 2 := by
          have _ : (sqrt u - sqrt v) ^ 2 ≥ 0 := sq_nonneg (sqrt u - sqrt v)
          have h10 : sqrt u * sqrt v ≤ (u + v) / 2 := by
            nlinarith [mul_self_nonneg (sqrt u * sqrt v),
                  Real.sq_sqrt (show 0 ≤ u by linarith [hu]), Real.sq_sqrt (show 0 ≤ v by linarith [hv])]
          linarith
        nlinarith [mul_nonneg (by linarith : 0 ≤ w) (by linarith : 0 ≤ (u + v) / 2),
            h8]
      nlinarith [h4, h5, h7, h2]
    -- Apply Cauchy-Schwarz inequality: (u+v+w)² ≥ 3(u*v + v*w + w*u)
    have h4 : (u + v + w) ^ 2 ≥ 3 * (u * v + v * w + w * u) := by
      nlinarith [sq_nonneg (u - v), sq_nonneg (v - w), sq_nonneg (w - u)]
    -- Combine previous inequalities to show (u+v+w)² ≥ 3
    have h5 : (u + v + w) ^ 2 ≥ 3 := by linarith [h3, h4]
    rw [show 3 = √3 ^ 2 by norm_num] at h5
    replace h5 : |u + v + w| ≥ |√3|:= by exact sq_le_sq.mp h5
    rw [abs_of_nonneg (by linarith)] at h5
    rw [abs_of_nonneg (by positivity)] at h5
    exact h5
