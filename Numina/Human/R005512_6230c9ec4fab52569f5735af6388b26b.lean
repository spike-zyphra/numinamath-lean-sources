import Mathlib

/- If $f(x) = x / (x + 1)$, what is $f(f(f(f(2009))))$? -/
theorem algebra_608579 {f : ℝ → ℝ} (hf : (x: ℝ) → (x ≠ -1) → f x = x / (x + 1)) :
    f (f (f (f (2009: ℝ)))) = 2009 / 8037 := by
  
  -- We can easily get $f(f(x))=\frac{(x /(x+1))}{(x /(x+1))+1}=x / 2 x+1$,
  have hf_comp (x : ℝ) (hx: x ≠ -1) (hfx: f x ≠ -1) : f (f x) = x / (2 * x + 1) := by
    rw [hf (f x) hfx, hf x hx];
    field_simp
    congr
    have : x + 1 ≠ 0 := by
      by_contra! hcx
      have : x = -1 := by linarith
      exact hx this
    calc
      _ = x * ((x + 1) / (x + 1)) + (x + 1)  := by ring
      _ = x * 1 + (x + 1)                    := by rw [(div_eq_one_iff_eq this).mpr]; simp
      _ = 2 * x + 1                          := by ring

  -- and simarlily $f(f(f(f(x))))=x / 4 x+1$.
  have hf_comp3 (x : ℝ) (hx: x ≠ -1) (hfx: f x ≠ -1) (hffx: f (f x) ≠ -1) 
      (hfffx: f (f (f x)) ≠ -1) : f (f (f (f x))) = x / (4 * x + 1) := by
    rw [hf_comp (f (f x)) hffx hfffx, hf_comp x hx hfx]
    rw [hf_comp x hx hfx] at hffx
    field_simp
    congr
    have : 2 * x + 1 ≠ 0 := by
      by_contra! hcx
      have : x = -1/2 := by linarith
      rw [hf x hx, this] at hfx
      field_simp at hfx
      rw [show (-2 + 1: ℝ) = -1 by ring] at hfx
      contradiction
    calc
      _ = (2 * x) * ((2 * x + 1) / (2 * x + 1)) + (2 * x + 1)  := by ring
      _ = (2 * x) * 1 + (2 * x + 1)                            := by
        rw [(div_eq_one_iff_eq this).mpr]; simp
      _ = 4 * x + 1                                            := by ring

  -- So $f(f(f(f(2009)))) = \frac{2009}{8037}$.
  specialize hf_comp 2009 (by linarith) (by rw [hf 2009 (by linarith)]; linarith)
  specialize hf_comp3 2009 
  rw [show (4 * 2009 + 1: ℝ) = 8037 by norm_num] at hf_comp3
  apply hf_comp3
  linarith
  rw [hf 2009 (by linarith)]; linarith
  rw [hf_comp]; linarith
  rw [hf (f (f 2009)), hf_comp]; linarith
  rw [hf_comp]; linarith
