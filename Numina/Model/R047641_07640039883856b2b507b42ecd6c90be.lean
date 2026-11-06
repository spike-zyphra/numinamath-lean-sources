import Mathlib

open Real

theorem algebra_599504
    : IsLeast {S : ℝ | ∃ u v w : ℝ, (0 < u ∧ 0 < v ∧ 0 < w ∧ u * sqrt (v * w) + v * sqrt (w * u) + w * sqrt (u * v) = 1 ∧ S = u + v + w)} (sqrt 3):= by
  constructor
  · -- Show that sqrt(3) is in the set
    use Real.sqrt 3 / 3, Real.sqrt 3 / 3, Real.sqrt 3 / 3
    constructor
    · -- Show u > 0
      have h1 : 0 < Real.sqrt 3 / 3 := by
        have h3 : Real.sqrt 3 > 0 := by positivity
        nlinarith
      linarith
    constructor
    · -- Show v > 0
      have h1 : 0 < Real.sqrt 3 / 3 := by
        have h3 : Real.sqrt 3 > 0 := by positivity
        nlinarith
      linarith
    constructor
    · -- Show w > 0
      have h1 : 0 < Real.sqrt 3 / 3 := by
        have h3 : Real.sqrt 3 > 0 := by positivity
        nlinarith
      linarith
    constructor
    · -- Show u * sqrt (v * w) + v * sqrt (w * u) + w * sqrt (u * v) = 1
      have h3 : Real.sqrt 3 > 0 := by positivity
      have h4 : Real.sqrt ((Real.sqrt 3 / 3) * (Real.sqrt 3 / 3)) = Real.sqrt 3 / 3 := by
        have h4 : (Real.sqrt 3 / 3 : ℝ) * (Real.sqrt 3 / 3) = (1 / 3 : ℝ) := by
          have h5 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
          nlinarith
        rw [h4]
        have h6 : Real.sqrt (1 / 3 : ℝ) = Real.sqrt 3 / 3 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> nlinarith
        linarith
      nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg (3 : ℝ)]
    · -- Show S = u + v + w
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  · -- Show sqrt(3) is the least such value
    intro S hS
    rcases hS with ⟨u, v, w, hu, hv, hw, he, hS⟩
    have h1 : 0 ≤ u := by linarith
    have h2 : 0 ≤ v := by linarith
    have h3 : 0 ≤ w := by linarith
    have h4 : 0 ≤ u * v := mul_nonneg (by linarith) (by linarith)
    have h5 : 0 ≤ v * w := mul_nonneg (by linarith) (by linarith)
    have h6 : 0 ≤ w * u := mul_nonneg (by linarith) (by linarith)
    have eq1 : sqrt (u * v) = sqrt u * sqrt v := by
      rw [Real.sqrt_mul (by nlinarith)]
    have eq2 : sqrt (v * w) = sqrt v * sqrt w := by
      rw [Real.sqrt_mul (by nlinarith)]
    have eq3 : sqrt (w * u) = sqrt w * sqrt u := by
      rw [Real.sqrt_mul (by nlinarith)]
    have h7 : u * Real.sqrt (v * w) + v * Real.sqrt (w * u) + w * Real.sqrt (u * v) = 1 := he
    rw [eq1] at h7
    rw [eq2] at h7
    rw [eq3] at h7
    have h8 : Real.sqrt u ≥ 0 := Real.sqrt_nonneg u
    have h9 : Real.sqrt v ≥ 0 := Real.sqrt_nonneg v
    have h10 : Real.sqrt w ≥ 0 := Real.sqrt_nonneg w
    have eq7 : u * (Real.sqrt v * Real.sqrt w) = (Real.sqrt u * Real.sqrt v * Real.sqrt w) * (Real.sqrt u) := by
      have h8 : (Real.sqrt u : ℝ) ^ 2 = u := Real.sq_sqrt (show (0 : ℝ) ≤ u by positivity)
      calc
        u * (Real.sqrt v * Real.sqrt w)
          = (Real.sqrt u ^ 2) * (Real.sqrt v * Real.sqrt w) := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ u by positivity)]
        _ = (Real.sqrt u * Real.sqrt v * Real.sqrt w) * (Real.sqrt u) := by ring
    have eq8 : v * (Real.sqrt w * Real.sqrt u) = (Real.sqrt u * Real.sqrt v * Real.sqrt w) * (Real.sqrt v) := by
      have h8 : (Real.sqrt v : ℝ) ^ 2 = v := Real.sq_sqrt (show (0 : ℝ) ≤ v by positivity)
      calc
        v * (Real.sqrt w * Real.sqrt u)
          = (Real.sqrt v ^ 2) * (Real.sqrt w * Real.sqrt u) := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ v by positivity)]
        _ = (Real.sqrt u * Real.sqrt v * Real.sqrt w) * (Real.sqrt v) := by ring
    have eq9 : w * (Real.sqrt u * Real.sqrt v) = (Real.sqrt u * Real.sqrt v * Real.sqrt w) * (Real.sqrt w) := by
      have h8 : (Real.sqrt w : ℝ) ^ 2 = w := Real.sq_sqrt (show (0 : ℝ) ≤ w by positivity)
      calc
        w * (Real.sqrt u * Real.sqrt v)
          = (Real.sqrt w ^ 2) * (Real.sqrt u * Real.sqrt v) := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ w by positivity)]
        _ = (Real.sqrt u * Real.sqrt v * Real.sqrt w) * (Real.sqrt w) := by ring
    have h9 : (Real.sqrt u * Real.sqrt v * Real.sqrt w) * (Real.sqrt u + Real.sqrt v + Real.sqrt w) = 1 := by
      linarith [h7, eq7, eq8, eq9]
    have h11 : u + v + w ≥ Real.sqrt 3 := by
      have h12 : u = (Real.sqrt u) ^ 2 := by
        rw [Real.sq_sqrt (show (0 : ℝ) ≤ u by positivity)]
      have h13 : v = (Real.sqrt v) ^ 2 := by
        rw [Real.sq_sqrt (show (0 : ℝ) ≤ v by positivity)]
      have h14 : w = (Real.sqrt w) ^ 2 := by
        rw [Real.sq_sqrt (show (0 : ℝ) ≤ w by positivity)]
      nlinarith [sq_nonneg (Real.sqrt u ^ 2 - Real.sqrt v ^ 2), sq_nonneg (Real.sqrt v ^ 2 - Real.sqrt w ^ 2), sq_nonneg (Real.sqrt w ^ 2 - Real.sqrt u ^ 2),
        sq_nonneg (Real.sqrt u * Real.sqrt v - Real.sqrt v * Real.sqrt w), sq_nonneg (Real.sqrt v * Real.sqrt w - Real.sqrt w * Real.sqrt u), sq_nonneg (Real.sqrt w * Real.sqrt u - Real.sqrt u * Real.sqrt v),
        mul_pos (show 0 < Real.sqrt u by apply Real.sqrt_pos.mpr (by positivity)) (show 0 < Real.sqrt v by apply Real.sqrt_pos.mpr (by positivity)),
        mul_pos (show 0 < Real.sqrt v by apply Real.sqrt_pos.mpr (by positivity)) (show 0 < Real.sqrt w by apply Real.sqrt_pos.mpr (by positivity)),
        mul_pos (show 0 < Real.sqrt u by apply Real.sqrt_pos.mpr (by positivity)) (show 0 < Real.sqrt w by apply Real.sqrt_pos.mpr (by positivity)),
        Real.sqrt_nonneg (u), Real.sqrt_nonneg (v), Real.sqrt_nonneg (w),
        mul_nonneg (Real.sqrt_nonneg u) (Real.sqrt_nonneg v),
        mul_nonneg (Real.sqrt_nonneg v) (Real.sqrt_nonneg w),
        mul_nonneg (Real.sqrt_nonneg w) (Real.sqrt_nonneg u),
        Real.mul_self_sqrt (show (0 : ℝ) ≤ (u : ℝ) by positivity),
        Real.mul_self_sqrt (show (0 : ℝ) ≤ (v : ℝ) by positivity),
        Real.mul_self_sqrt (show (0 : ℝ) ≤ (w : ℝ) by positivity),
        Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
      ]
    nlinarith