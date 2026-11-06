import Mathlib

noncomputable def cubic_root (x : ℝ) : ℝ :=
  if 0 ≤ x
  then Real.rpow x (1 / 3)
  else -Real.rpow (-x) (1 / 3)

/- Find all real numbers $x$ satisfying the equation $x^{3}-8=16 \sqrt[3]{x+1}$.-/
theorem algebra_609691 :
    {x : ℝ | x ^ 3 - 8 = 16 * cubic_root (x + 1)} = {-2, 1 - Real.sqrt 5, 1 + Real.sqrt 5} := by
  -- Let f(x) = x³ - 8 / 8.
  let f (x : ℝ) := (x ^ 3 - 8) / 8
  -- Show that f(2(x + 1)^(1 / 3)) = x for all ax.
  have h₀ (x : ℝ) : f (2 * cubic_root (x + 1)) = x := by
    simp [f]
    rw [mul_pow, cubic_root]
    split_ifs with hx
    . norm_num
      rw [<-Real.rpow_natCast, <-Real.rpow_mul hx]
      norm_num
      ring
    . rw [neg_pow]
      norm_num
      rw [<-Real.rpow_natCast, <-Real.rpow_mul (by linarith)]
      norm_num
      ring
  -- Show that f is strictly monotone.
  have h₁ : StrictMono f := by
    rintro a b hab
    suffices a ^ 3 < b ^ 3 by
      simp [f]
      linarith only [this]
    exact Odd.strictMono_pow (by simp [Odd]) hab
  -- Show that f is injective because f is strictly monotone.
  have h₂ : Function.Injective f := StrictMono.injective h₁
  -- Break the goal into two parts.
  ext x
  simp
  apply Iff.intro
  . -- Show that the equation implies the solutions.
    intro h
    replace h : f x = 2 * cubic_root (x + 1) := by
      simp [f]
      linarith only [h]
    -- Note that this implies that f(f(x)) = x.
    have h' : f (f x) = x := by
      rw [h]
      apply h₀
    -- Show that f(x) ≤ x.
    have h₃ : f x ≤ x := by
      -- Assume on the contrary that f(x) > x, then f(f(x)) > f(x) > x.
      by_contra! h''
      have h''' := h₁ h''
      linarith
    -- Show that f(x) ≥ x.
    have h₄ : f x ≥ x := by
      -- Assume on the contrary that f(x) < x, then f(f(x)) < f(x) < x.
      by_contra! h''
      have h''' := h₁ h''
      linarith
    -- Show that f(x) = x.
    replace h' : f x = x := by
      linarith
    clear h₃ h₄
    -- Now it suffices to solve f(x) = x.
    simp [f] at h'
    replace h' : (x + 2) * (x - (1 - Real.sqrt 5)) * (x - (1 + Real.sqrt 5)) = 0 := by
      ring_nf
      field_simp
      linarith only [h']
    simp at h'
    -- Now the goal is trivial.
    obtain (h' | h') | h' := h'
    . left
      linarith
    . right
      left
      linarith
    . right
      right
      linarith
  . intro h
    obtain h | h | h := h
    . -- If x = -2, the equation is satisfied.
      rw [h]
      simp [cubic_root]
      norm_num
    all_goals
      -- If x = 1 ± √5, the equation is satisifed.
      -- We first find that f(x) = x.
      have h' : f x = x := by
        rw [h]
        simp [f]
        ring_nf
        rw [show Real.sqrt 5 ^ 3 = Real.sqrt 5 * Real.sqrt 5 ^ 2 by ring_nf]
        field_simp
        ring_nf
      -- We then find that f(f(x)) = x = f (2 * cubic_root (x + 1)).
      have h'' : f (f x) = f (2 * cubic_root (x + 1)) := by
        have h'' := congr_arg (f ·) h'
        simp at h''
        exact (h''.trans h').trans (h₀ x).symm
      -- Since f is injective, we have f(x) = 2 * cubic_root (x + 1), and the goal is obvious.
      apply h₂ at h''
      simp [f] at h''
      linarith only [h'']
