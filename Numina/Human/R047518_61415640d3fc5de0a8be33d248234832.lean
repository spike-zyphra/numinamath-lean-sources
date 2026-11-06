import Mathlib

open Complex

/- 5. If the complex number $z$ satisfies

$$

\left|\frac{z^{2}+1}{z+\mathrm{i}}\right|+\left|\frac{z^{2}+4 \mathrm{i}-3}{z-\mathrm{i}+2}\right|=4 \text {, }

$$


then the minimum value of $\mid z-1$ | is -/
theorem algebra_227350 : IsLeast {Complex.abs (z - 1) | (z : ℂ) (_ : Complex.abs ((z ^ 2 + 1) / (z + I)) + Complex.abs ((z ^ 2 + 4 * I - 3) / (z - I + 2)) = 4)} (√2) := by
  constructor
  -- we first prove √2 is achievable by using z = 2 + I, mostly simplification
  . simp
    use 2 + I
    ring_nf
    simp [Complex.abs, normSq]
    ring_nf
    simp
    rw [← Real.sqrt_inv, ← Real.sqrt_mul (by norm_num)]
    norm_num
    rw [show (4:ℝ) = 2^2 by norm_num]
    simp
    norm_num
  -- now we show √2 is a lower bound
  . rintro a ⟨z, hz, ha⟩
    rw [← ha]
    clear ha
    -- first of all change the ratios to z - something
    have h₁ : z + I ≠ 0 := by
      by_contra h₁
      replace h₁ : z = - I := by linear_combination h₁
      rw [h₁] at hz
      ring_nf at hz
      simp [Complex.abs, normSq] at hz
      ring_nf at hz
      rw [show (4 : ℝ) = 2^2 by norm_num] at hz
      simp at hz
      norm_num at hz
    have h₂ : z - I + 2 ≠ 0 := by
      by_contra h₂
      replace h₂ : z = I - 2 := by linear_combination h₂
      rw [h₂] at hz
      ring_nf at hz
      simp [Complex.abs, normSq] at hz
      ring_nf at hz
      rw [show (4 : ℝ) = 2^2 by norm_num] at hz
      simp at hz
      norm_num at hz
    replace h₁ : (z ^ 2 + 1) / (z + I) = z - I := by
      field_simp; ring_nf; simp; ring
    replace h₂ : (z ^ 2 + 4 * I - 3) / (z - I + 2) = z + I - 2 := by
      field_simp; ring_nf; simp; ring
    rw [h₁, h₂] at hz
    -- now we show a lemma that |z-a+b| + |z-a-b| = c implies c^2/4 - |b|^2 ≤ |z-a|^2, geometrically this is stating semi minor axis of ellipse is the smallest of the distances from a point to center
    have aux (z a b : ℂ) (c : ℝ) (h : Complex.abs (z - a + b) + Complex.abs (z - a - b) = c) :
      c^2 / 4 - normSq b  ≤ Complex.abs (z - a) ^ 2 := by
      -- we prove this from the inequaliy that 0 ≤ (|z-a+b| - |z-a-b|)^2
      replace h' : 0 ≤ (Complex.abs (z - a + b) - Complex.abs (z - a - b))^2 := by positivity
      replace h' : (Complex.abs (z - a + b) + Complex.abs (z - a - b)) ^ 2 ≤ 2 * (Complex.abs (z - a + b) ^ 2 + Complex.abs (z - a - b) ^ 2) := by linear_combination h'
      rw [h, Complex.sq_abs, Complex.sq_abs, Complex.normSq_add, Complex.normSq_sub (z - a)] at h'
      ring_nf at h'
      rw [← Complex.sq_abs] at h'
      linear_combination h'/4
    -- now we prove squared version of the goal by using lemma on z, a = 1 b = (1 - I), c = 4
    apply sq_le_sq₀ (by positivity) (by positivity) |>.mp
    have := aux z 1 (1 - I) 4 (by ring_nf at hz ⊢; assumption)
    convert this
    simp [normSq]
    norm_num