import Mathlib

theorem inequalities_29694 (c : ℝ) :
    (∀ a b : ℝ, (c ^ 2 - 2 * a * c + b) * ((-c) ^ 2 - 2 * a * (-c) + b) ≥
      (a ^ 2 - 2 * a * a + b)) ↔ c = 1 / 2 ∨ c = -1 / 2 := by

  constructor
  · -- Forward direction: if the inequality holds for all a and b, then c in {-1/2,1/2}
    intro h
    have h1 : ∀ a b : ℝ, (c ^ 2 - 2 * a * c + b) * ((-c) ^ 2 - 2 * a * (-c) + b) ≥ a ^ 2 - 2 * a * a + b := by
      intro a b
      have h2 := h a b
      simpa using h2
    have h4 := h1 c (1 / 4)
    ring_nf at h4
    have h5 : c^2 = 1/4 := by
      nlinarith [ sq_nonneg (c ^ 2 - 1 / 4), sq_nonneg (c ^ 2 * 4 - 1) ]
    have hc1 : c=1/2 ∨ c=-1/2 := by
      have hc2 :c^2 =1/4:=h5
      have hc3 :c= 1/2 ∨ c=-1/2 := by
        have hc4 :c^2-(1/4)=0:= by linarith
        have hc5 : (c-1/2)*(c+1/2)=0 := by
          nlinarith
        cases (mul_eq_zero.1 hc5) with
        | inl h => 
          left 
          linarith
        | inr h => 
          right 
          linarith
      assumption
    assumption
  · -- Backward direction: if c in {-1/2,1/2}, then the inequality holds for all a and b
    rintro (hc | hc )
    · -- Case c = 1/2
      intro a b
      rw [hc]
      nlinarith [ sq_nonneg (b - 1 / 4), sq_nonneg (a - 1 / 2), sq_nonneg (a + 1 / 2), sq_nonneg (b - 1 / 4) ]
    · -- Case c = -1/2
      intro a b
      rw [hc]
      nlinarith [ sq_nonneg (b - 1 / 4), sq_nonneg (a - 1 / 2), sq_nonneg (a + 1 / 2), sq_nonneg (b - 1 / 4) ]