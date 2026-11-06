import Mathlib

open Real

/- Let $f(x) = \left\lceil\dfrac{1}{x+2}\right\rceil$ for $x > -2$, and $f(x) = \left\lfloor\dfrac{1}{x+2}\right\rfloor$ for $x < -2$. ($f(x)$ is not defined at $x = -2$.) Which integer is not in the range of $f(x)$?-/
theorem algebra_10261 (f : ℝ → ℤ) (hf : ∀ x, x > -2 → f x = ⌈1 / (x + 2)⌉) (hf' : ∀ x, x < -2 → f x = ⌊1 / (x + 2)⌋) :
    {0} = {n | ¬ ∃ x ≠ -2, f x = n} := by
  -- simplify the set
  ext n
  -- split the goal into two
  constructor <;> intro h
  . -- one side
    -- firstly simplify the hypothesis
    simp at h ⊢
    rw [h]
    -- prove by contradiction
    by_contra hx
    simp at hx
    -- simplify hx
    obtain ⟨x, hx1, hx2⟩ := hx
    -- discuss the sign of x + 2
    by_cases h2 : x > -2
    . -- x > -2
      specialize hf x h2
      -- simplify the hypothesis
      replace h2 : - (x + 2) < 0 := by linarith
      rw [hx2] at hf
      -- use the fundamental inequality of ceil
      have h1 : 1 / (x + 2) ≤ ⌈1 / (x + 2)⌉ := Int.le_ceil _
      -- derive a contradiction
      rw [← hf] at h1
      simp at h1
      linarith
    . -- x < -2
      replace h2 : x < -2 := lt_of_le_of_ne (by linarith : x ≤ -2) (by simp [hx1])
      specialize hf' x h2
      -- simplify the hypothesis
      replace h2 : - (x + 2) > 0 := by linarith
      -- use the fundamental inequality of floor
      have h1 : ⌊1 / (x + 2)⌋ ≤ 1 / (x + 2) := Int.floor_le _
      -- derive a contradiction
      rw [hx2] at hf'
      rw [← hf'] at h1
      simp at h1
      linarith

  . -- the other side
    simp at h
    -- prove by contradiction
    by_contra hn
    -- discuss the sign of n
    by_cases hn0 : n > 0
    . -- n > 0
      -- specialize at x = 1 / n - 2
      let x : ℝ := 1 / (n : ℝ) - 2
      have hx : x = 1 / (n : ℝ) - 2 := rfl
      specialize h x
      -- prove that x > -2
      have hx2 : x > -2 := by
        simp [x]
        linarith
      -- use the definition of f
      specialize hf x hx2
      -- plug in the value of x
      nth_rw 2 [hx] at hf
      -- prove that f x = n
      simp at hf
      -- derive a contradiction
      replace h : ¬ f x = n := h (by linarith : x ≠ -2)
      contradiction
    . -- n ≤ 0
      -- derive n < 0
      replace hn : n ≠ 0 := by
        simp at hn
        exact hn
      replace h2 : n < 0 := lt_of_le_of_ne (by linarith : n ≤ 0) (hn)
      -- change the type of n
      replace h2 : (n : ℝ) < 0 := by norm_cast
      -- specialize at x = 1 / n - 2
      let x : ℝ := 1 / n - 2
      have hx : x = 1 / n - 2 := rfl
      specialize h x
      -- prove that x < -2
      have hx2 : x < -2 := by
        rw [hx] -- plug the expression of x
        calc 1 / (n : ℝ) - 2 < 0 - 2 := sub_lt_sub_right (one_div_neg.mpr (h2)) 2 -- use the fact that n < 0
          _ = -2 := by norm_num
      -- plug x in and use the definition of f
      specialize hf' x hx2
      nth_rw 2 [hx] at hf'
      -- prove that f x = n
      simp at hf'
      -- derive a contradiction
      replace h : ¬ f x = n := h (by linarith : x ≠ -2)
      contradiction
