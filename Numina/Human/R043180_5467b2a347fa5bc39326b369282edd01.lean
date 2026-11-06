import Mathlib
/- 3. Let the function $f(x)$ have the domain $\mathbf{R}$, and when $x \geqslant 0$, $f(x)=|x-2|+a$ (where $a$ is a real number). If $f(x)$ is an odd function, then the solution set of the inequality $f(x) \geqslant 1$ is $\qquad$ . -/
theorem algebra_184863 {f : ℝ → ℝ} (hf : ∀ x, x ≥ 0 → f x = |x - 2| + a) (ha : ∀ x, f (-x) = -f x) :
{x | f x ≥ 1} = {x | x ∈ Set.Icc (-3) (-1) ∨ x ∈ Set.Ici 5}:= by
  ext x
  -- Apply the odd function property to x = 0
  have ha1:= ha 0
  simp at ha1
  -- Since f is odd, f(0) = 0
  replace ha1 : f 0 = 0:= by linarith
  -- Determine the value of parameter a
  replace ha1 : a = -2:= by
    specialize hf 0 (by norm_num)
    norm_num at hf
    linarith
  subst a
  constructor
  -- Forward direction: if f(x) ≥ 1, then x ∈ [-3,-1] or x ≥ 5
  .
    intro h
    simp at h
    -- Case analysis based on whether x is non-negative
    by_cases hx : x ≥ 0
    -- Case: x ≥ 0
    .
      specialize hf x hx
      replace hf : |x - 2| ≥ 3:= by linarith
      -- Further case analysis based on x - 2
      by_cases hx1 : x - 2 ≥ 0
      -- Case: x - 2 ≥ 0, which means x ≥ 2
      .
        rw [abs_of_nonneg hx1] at hf
        simp
        right
        linarith
      -- Case: x - 2 < 0, which means 0 ≤ x < 2
      .
        simp at hx1
        replace hx1 : x - 2 < 0:= by linarith
        rw [abs_of_neg hx1] at hf
        linarith
    -- Case: x < 0
    .
      simp at hx
      specialize hf (-x) (by linarith)
      specialize ha x
      rw [ha] at hf
      replace hf : |-x - 2| ≤ 1:= by linarith
      -- Further case analysis based on -x - 2
      by_cases hx1 : -x - 2 ≥ 0
      -- Case: -x - 2 ≥ 0, which means x ≤ -2
      .
        rw [abs_of_nonneg hx1] at hf
        simp
        left
        refine ⟨(by linarith), (by linarith)⟩
      -- Case: -x - 2 < 0, which means x > -2
      .
        simp at hx1
        replace hx1 : -x - 2 < 0:= by linarith
        rw [abs_of_neg hx1] at hf
        ring_nf at hf
        simp
        left
        refine ⟨(by linarith), (by linarith)⟩
  -- Reverse direction: if x ∈ [-3,-1] or x ≥ 5, then f(x) ≥ 1
  .
    intro h
    simp at h
    rcases h with h | h
    -- Case: x ∈ [-3,-1]
    .
      rcases h with ⟨h1, h2⟩
      simp
      specialize hf (-x) (by linarith)
      specialize ha x
      rw [ha] at hf
      replace h1 : x + 3 ≥ 0:= by linarith
      replace h2 : -x - 1 ≥ 0:= by linarith
      have h3 : (x + 3) * (-x - 1) ≥ 0:= by positivity
      replace h3 : (-x - 2) ^ 2 ≤ 1 ^ 2:= by linarith
      replace h3 : |-x - 2| ≤ |1|:= by exact sq_le_sq.mp h3
      norm_num at h3
      linarith
    -- Case: x ≥ 5
    .
      specialize hf x (by linarith)
      rw [abs_of_nonneg (by linarith)] at hf
      simp
      linarith
