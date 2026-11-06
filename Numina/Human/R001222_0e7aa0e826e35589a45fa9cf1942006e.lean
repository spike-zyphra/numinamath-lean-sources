import Mathlib

/- The equation \[2000x^6+100x^5+10x^3+x-2=0\]has two real roots. Compute the square of the difference between them. -/
theorem algebra_21590 (f : ℝ → ℝ) (hf : f = fun x => 2000*x^6 + 100*x^5 + 10*x^3 + x - 2) (r1 r2 : ℝ) (hr1 : f r1 = 0) (hr2 : f r2 = 0) (hr : r1 ≠ r2) : (r1 - r2)^2 = 161/400 := by
  
  -- Factorize the polynomial $f(x) = (20 * x^2 + x - 2) * (100 * x^4 + 10 * x^2 + 1)$
  have h1 : ∀ x, f x = (100 * x^4 + 10 * x^2 + 1) * (20 * x^2 + x - 2) := by
    intro x
    simp only [hf]
    ring
  
  -- Show that $100x^4 + 10x^2 + 1$ is positive for all real $x$
  have h2 : ∀ (x : ℝ), 100 * x^4 + 10 * x^2 + 1 > 0 := by
    intro x
    apply add_pos_of_nonneg_of_pos
    apply add_nonneg
    apply mul_nonneg
    norm_num
    refine Even.pow_nonneg ?_ x
    exact Nat.even_iff.mpr rfl
    norm_num
    exact sq_nonneg x
    exact Real.zero_lt_one
  
  -- The quadratic equation $20x^2 + x - 2 = 0$
  have h3 : ∀ x, f x = 0 → 20 * x^2 + x - 2 = 0 := by
    intro x hfx
    have mid : 100 * x^4 + 10 * x^2 + 1 ≠ 0 := by
      apply ne_of_gt
      exact h2 x
    refine eq_zero_of_ne_zero_of_mul_left_eq_zero mid ?_
    have mid : f x = (100 * x^4 + 10 * x^2 + 1) * (20 * x^2 + x - 2) := h1 x
    rw [mid.symm, hfx]
  
  -- Solve $20x^2 + x - 2 = 0$
  have h4 : ∀ x : ℝ, 20 * x^2 + x - 2 = 0 → x = (-1 + √161) / 40 ∨ x = (-1 - √161) / 40 := by
    intro x
    intro heq
    have mid : 20 * x^2 + x - 2 = 20 * (x - (-1 + √161) / 40) * (x - (-1 - √161) / 40) := by
      ring_nf
      rw [Real.sq_sqrt]
      ring
      exact Nat.ofNat_nonneg' 161
    rw [heq] at mid
    simp only [zero_eq_mul, mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at mid
    rcases mid with mid | mid
    left
    apply eq_of_sub_eq_zero at mid
    exact mid
    right
    apply eq_of_sub_eq_zero at mid
    exact mid
  
  -- Calculate the difference between the roots
  have h5 : (r1 - r2)^2 = (√161 / 20)^2 := by
    have h51 : 20 * r1^2 + r1 - 2 = 0 := h3 r1 hr1
    have h52 : 20 * r2^2 + r2 - 2 = 0 := h3 r2 hr2
    rcases h4 r1 h51 with h12 | h12
    rcases h4 r2 h52 with h13 | h13
    rw [h13.symm] at h12
    contradiction
    rw [h12, h13]
    ring
    rcases h4 r2 h52 with h13 | h13
    rw [h13, h12]
    ring
    rw [h13.symm] at h12
    contradiction

  
  -- Simplify the final result
  rw [h5]
  ring_nf
  norm_num

