import Mathlib

open Set Real

theorem algebra_21064 {f : ℝ → ℝ} (hf : ∀ x, x ≤ 0 → f x = x ^ 2)
    (hf' : ∀ x, x > 0 → f x = x ^ 3 - 5) :
    range f = {y | y > -5} := by
  ext y
  simp only [mem_range, mem_setOf_eq]
  constructor
  · -- Assume y in range of f
    rintro ⟨x, hx⟩
    by_cases h : x ≤ 0
    · -- If x ≤ 0, then f(x) = x^2
      have hx1 : f x = x ^ 2 := hf x h
      rw [hx1] at hx
      nlinarith [sq_nonneg x]
    · -- If x > 0, then f(x) = x^3 - 5
      have hx2 : x > 0 := by linarith
      have hx3 : f x = x ^ 3 - 5 := hf' x hx2
      rw [hx3] at hx
      nlinarith [sq_nonneg (x ^ 2), sq_pos_of_pos (show 0 < x by linarith)]
  · -- Assume y > -5, need to find x such that f(x) = y
    intro hy
    by_cases h : y ≥ 0
    · -- If y ≥ 0, use x = -sqrt(y) ≤ 0
      use -Real.sqrt y
      have h1 : (-Real.sqrt y) ≤ 0 := by
        have : Real.sqrt y ≥ 0 := Real.sqrt_nonneg y
        linarith [Real.sqrt_nonneg y]
      rw [hf (-Real.sqrt y) h1]
      have h2 : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt (by linarith)
      nlinarith [Real.sqrt_nonneg y, h2]
    · -- If y < 0, use x > 0 such that x^3 - 5 = y
      have h2 : y > -5 := by linarith
      use (y + 5) ^ (1 / 3 : ℝ)
      have h3 : (y + 5) ^ (1 / 3 : ℝ) > 0 := by
        apply Real.rpow_pos_of_pos
        linarith
      rw [hf' ((y + 5) ^ (1 / 3 : ℝ)) (by linarith)]
      have h4 : ((y + 5) ^ (1 / 3 : ℝ)) ^ 3 = y + 5 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals linarith
      nlinarith [h4]