import Mathlib

open Real Set
open scoped Real

theorem algebra_92962 (x : ℝ) (hx : x ∈ Ico 0 Real.pi) (h : sin x + cos x = 1 / 5) :
    tan x = -4 / 3 := by 
  rcases hx with ⟨hx1, hx2⟩
  have h1 : 0 ≤ x := hx1
  have h2 : x < Real.pi := hx2
  have h3 : sin x ≥ 0 := by 
    apply sin_nonneg_of_nonneg_of_le_pi
    nlinarith [h1, h2, Real.pi_gt_three]
    nlinarith [h1, h2, Real.pi_gt_three]
  have h4 : sin x = 1 / 5 - cos x := by 
    linarith 
  have h5 : sin x ^ 2 + cos x ^ 2 = 1 := by 
    exact Real.sin_sq_add_cos_sq x 
  rw [h4] at h5
  -- Solving quadratic $50 * \cos^2 x - 10 * \cos x - 24 = 0$.
  have h6 : 50 * cos x ^ 2 - 10 * cos x - 24 = 0 := by 
    nlinarith [h5, Real.sin_sq_add_cos_sq x, h4]
  have h7 : (cos x - 4 / 5) * (cos x + 3 / 5) = 0 := by 
    nlinarith [h6]
  have h8 : cos x = 4 / 5 ∨ cos x = -3 / 5 := by 
    cases (mul_eq_zero.mp h7) with 
    | inl h9 => 
      left 
      linarith
    | inr h10 => 
      right 
      nlinarith 
  cases h8 with 
  | inl h9 => 
    have h9 : cos x = 4 / 5 := by linarith 
    have h10 : sin x = -3 / 5 := by 
      nlinarith [h4, h9]
    linarith [h10, h3]
  | inr h9 => 
    have h9 : cos x = -3 / 5 := by linarith 
    have h10 : sin x = 4 / 5 := by 
      nlinarith [h4, h9]
    rw [tan_eq_sin_div_cos]
    -- Therefore $\tan x = \frac{\sin x}{\cos x} = \frac{4/5}{-3/5} = -\frac{4}{3}$.
    -- $\sin x = \frac{4}{5}$, $\cos x = -\frac{3}{5}$ is valid.
    rw [h9, h10]
    all_goals 
      nlinarith