import Mathlib

open Real Set

theorem algebra_296318 :
    IsLeast {x : ℝ | ∃ s : ℝ, ∃ t : ℝ, x = (s + 5 - 3 * abs (cos t))^2 + (s - 2 * abs (sin t))^2} 2 := by
  constructor
  · -- Show 2 is in the set
    use -1, (0 : ℝ)
    have h1 : cos (0 : ℝ) = 1 := by
      simp [cos_zero]
    have h2 : sin (0 : ℝ) = 0 := by
      simp [sin_zero]
    have h3 : abs (cos (0 : ℝ)) = 1 := by
      rw [h1]
      norm_num
    have h4 : abs (sin (0 : ℝ)) = 0 := by
      rw [h2]
      norm_num
    rw [h3, h4]
    norm_num
  · -- Show no value less than 2 is in the set
    intro x hx
    rcases hx with ⟨s, t, heq⟩
    have h1 : 0 ≤ abs (cos t) := abs_nonneg (cos t)
    have h2 : 0 ≤ abs (sin t) := abs_nonneg (sin t)
    have h3 : (cos t) ^ 2 + (sin t) ^ 2 = 1 := by
      exact Real.cos_sq_add_sin_sq t
    have h4 : (abs (cos t)) ^ 2 + (abs (sin t)) ^ 2 = 1 := by
      have h1' : abs (cos t) ^ 2 = (cos t) ^ 2 := by
        simp [abs_sq]
      have h2' : abs (sin t) ^ 2 = (sin t) ^ 2 := by
        simp [abs_sq]
      nlinarith
    have h6 : 0 ≤ abs (cos t) := by apply abs_nonneg
    have h7 : 0 ≤ abs (sin t) := by apply abs_nonneg
    nlinarith [sq_nonneg (s + 1), sq_nonneg (abs (cos t) - 1), sq_nonneg (abs (sin t) - 0), sq_nonneg (2 * abs (cos t) - 3 * abs (sin t)), abs_nonneg (cos t), abs_nonneg (sin t)]