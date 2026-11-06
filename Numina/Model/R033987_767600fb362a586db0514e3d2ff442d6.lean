import Mathlib

theorem algebra_235828 (x y : ℝ) :
    y^2 - abs y = x^2 - abs x ↔ (abs y + abs x = 1 ∨ abs y = abs x) := by
  constructor
  · -- Assume y^2 - abs y = x^2 - abs x prove abs y + abs x = 1 ∨ abs y = abs x
    intro h
    by_cases hy : y ≥ 0
    · -- Case y ≥ 0
      rw [abs_of_nonneg hy] at h
      by_cases hx : x ≥ 0
      · -- Case x ≥ 0, y ≥ 0.
        rw [abs_of_nonneg hx] at h
        by_cases h1 : y = x
        · -- Case y = x.
          right
          rw [abs_of_nonneg hy, abs_of_nonneg hx]
          linarith
        · -- Case y ≠ x.
          have h2 : y + x = 1 := by
            have h3 : y ≠ x := by 
              intro heq
              apply h1
              linarith
            have h4 : y^2 - y = x^2 - x := by linarith
            have h5 : (y + x) * (y - x) = (y - x) := by
              nlinarith
            have h6 : y - x ≠ 0 := by
              intro h7
              apply h3
              linarith
            have h7 : y + x = 1 := by
              apply (mul_right_inj' h6).mp
              linarith
            exact h7
          left
          rw [abs_of_nonneg hy, abs_of_nonneg hx]
          linarith
      · -- Case x < 0, y ≥ 0.
        rw [abs_of_neg (show x < 0 by linarith)] at h
        have : y = x + 1 ∨ y = -x := by
          have h_eq : (y - 1/2)^2 = (x + 1/2)^2 := by
            nlinarith
          cases (sq_eq_sq_iff_eq_or_eq_neg.mp h_eq) with
          | inl h3 =>
            left
            linarith
          | inr h4 =>
            right
            linarith
        cases this with
        | inl h_eq2 =>
          -- Now have y = x + 1. Need then |y|+|x|=1.
          left
          rw [abs_of_nonneg hy, abs_of_neg (show x < 0 by linarith)]
          nlinarith
        | inr h_eq_ymx =>
          right
          rw [abs_of_nonneg hy, abs_of_neg (show x < 0 by linarith)]
          linarith
    · -- Case y < 0
      rw [abs_of_neg (show y < 0 by linarith)] at h
      by_cases hx : x ≥ 0
      · -- Case x ≥ 0, y < 0.
        rw [abs_of_nonneg hx] at h
        have : x = y + 1 ∨ x = -y := by
          have h_eq : (x - 1/2)^2 = (y + 1/2)^2 := by
            nlinarith
          cases (sq_eq_sq_iff_eq_or_eq_neg.mp h_eq) with
          | inl h3 =>
            left
            linarith
          | inr h4 =>
            right
            nlinarith
        cases this with
        | inl h_eq_x =>
          -- Now x = y + 1. Derive from, with y < 0 => y+x=0 impossible. Then the goal.
          left
          rw [abs_of_neg (show y < 0 by linarith), abs_of_nonneg hx]
          nlinarith
        | inr h_eq_xm_y =>
          right
          rw [abs_of_neg (show y < 0 by linarith), abs_of_nonneg hx]
          linarith
      · -- Case x < 0, y < 0.
        rw [abs_of_neg (show x < 0 by linarith)] at h
        by_cases h1 : y = x
        · -- Case y = x.
          right 
          rw [abs_of_neg (show y < 0 by linarith), abs_of_neg (show x < 0 by linarith)]
          linarith
        · -- Case y ≠ x.
          -- Then from h have.
          have h_eq : (y + x + 1) * (y - x) = 0 := by 
            nlinarith
          cases' (mul_eq_zero.mp h_eq) with h2 h3
          · -- Case y + x + 1 = 0. So |y|+|x|=1.
            left 
            rw [abs_of_neg (show y < 0 by linarith), abs_of_neg (show x < 0 by linarith)]
            nlinarith
          · -- Case y - x = 0. So y = x.
            exfalso 
            apply h1
            linarith
  · -- Assume (abs y + abs x = 1 ∨ abs y = abs x) prove y^2 - abs y = x^2 - abs x
    rintro (h | h)
    · -- Case abs y + abs x = 1.
      by_cases hy : y ≥ 0
      · -- Case y ≥ 0.
        rw [abs_of_nonneg hy] at h 
        by_cases hx : x ≥ 0
        · -- Case x ≥ 0.
          rw [abs_of_nonneg hx] at h 
          rw [abs_of_nonneg hy, abs_of_nonneg hx]
          nlinarith [sq_nonneg (y - x), sq_nonneg (y + x - 1)]
        · -- Case x < 0.
          rw [abs_of_neg (show x < 0 by linarith)] at h 
          rw [abs_of_nonneg hy, abs_of_neg (show x < 0 by linarith)]
          nlinarith [sq_nonneg (y + x + 1), sq_nonneg (y + x)]
      · -- Case y < 0.
        rw [abs_of_neg (show y < 0 by linarith)] at h 
        by_cases hx : x ≥ 0
        · -- Case x ≥ 0.
          rw [abs_of_nonneg hx] at h 
          rw [abs_of_neg (show y < 0 by linarith), abs_of_nonneg hx]
          nlinarith [sq_nonneg (y + x - 1), sq_nonneg (-y - x - 1)]
        · -- Case x < 0.
          rw [abs_of_neg (show x < 0 by linarith)] at h 
          rw [abs_of_neg (show y < 0 by linarith), abs_of_neg (show x < 0 by linarith)]
          nlinarith [sq_nonneg (y - x), sq_nonneg (y + x + 1)]
    · -- Case abs y = abs x.
      by_cases hy : y ≥ 0
      · -- Case y ≥ 0.
        rw [abs_of_nonneg hy] at h 
        by_cases hx : x ≥ 0
        · -- Case x ≥ 0.
          rw [abs_of_nonneg hx] at h 
          rw [abs_of_nonneg hy, abs_of_nonneg hx]
          nlinarith [sq_nonneg (y - x), sq_nonneg (y + x)]
        · -- Case x < 0.
          rw [abs_of_neg (show x < 0 by linarith)] at h 
          rw [abs_of_nonneg hy, abs_of_neg (show x < 0 by linarith)]
          nlinarith [sq_nonneg (y + x + 1), sq_nonneg (y - (-x))]
      · -- Case y < 0.
        rw [abs_of_neg (show y < 0 by linarith)] at h 
        by_cases hx : x ≥ 0
        · -- Case x ≥ 0.
          rw [abs_of_nonneg hx] at h 
          rw [abs_of_neg (show y < 0 by linarith), abs_of_nonneg hx]
          nlinarith [sq_nonneg (y + x), sq_nonneg ((-y) - x)]
        · -- Case x < 0.
          rw [abs_of_neg (show x < 0 by linarith)] at h 
          rw [abs_of_neg (show y < 0 by linarith), abs_of_neg (show x < 0 by linarith)]
          nlinarith [sq_nonneg ((-y) - (-x)), sq_nonneg (y + x)]