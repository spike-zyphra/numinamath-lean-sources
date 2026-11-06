import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_306453 {x : ℝ} (hx : x ∈ Ioo 0 (π/2)) (h : 6 * cos x = 5 * tan x)
  (P : ℝ × ℝ) (hP : P = (x, 6 * cos x)) (P1 : ℝ × ℝ)
  (hP1 : P1 = (x, 0)) (P2 : ℝ × ℝ) (hP2 : P2 = (x, sin x)) :
  dist P1 P2 = 2/3 := by
    rcases hx with ⟨hx1, hx2⟩
    have h1 : sin x > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [hx1, hx2]
      linarith [hx1, hx2]
    have h1' : cos x > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      linarith [hx1, hx2]
      linarith [hx1, hx2]
    --Now we convert $\tan x$ to $\frac{\sin x}{\cos x}$. 
    have htan : tan x = sin x / cos x := by
      rw [tan_eq_sin_div_cos]
    rw [htan] at h
    -- Now h is $6 \cos x = 5 \cdot \frac{\sin x}{\cos x}$
    -- We can multiply both sides by $\cos x$ (positive) to get $6 \cos^2 x = 5 \sin x$
    have h2 : 6 * cos x ^ 2 = 5 * sin x := by
      have hcos : cos x ≠ 0 := by nlinarith
      field_simp at h
      nlinarith 
    have h3 : cos x ^ 2 = 1 - sin x ^ 2 := by
      have hcos : cos x ^ 2 + sin x ^ 2 = 1 := by
        exact Real.cos_sq_add_sin_sq x
      nlinarith 
    -- Therefore the vertical distance from $y = \sin x$ to $y = 0$ is $ \boxed{\dfrac{2}{3}} $
    rw [h3] at h2 
    have h5 : sin x = 2 / 3 := by 
      have h8 : (3 * sin x - 2) * (2 * sin x + 3) = 0 := by
        nlinarith 
      cases' (mul_eq_zero.mp h8) with h9 h10 
      · -- Case where $\sin x = \frac{2}{3}$.
        linarith
      · -- Case where $\sin x = -\frac{3}{2}$ contradicts $\sin x > 0$.
        nlinarith [h1] 
    rw [hP1] at *
    rw [hP2] at *
    simp [dist, h5, abs_of_nonneg (show sin x ≥ 0 by nlinarith)]
    all_goals linarith