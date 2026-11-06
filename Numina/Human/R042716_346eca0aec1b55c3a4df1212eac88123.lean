import Mathlib
open Real Set
open scoped BigOperators

/- If $f(x)=\dfrac{x-3}{x-4}$, then for what value of $x$ is $f^{-1}(x)$ undefined?-/
theorem algebra_945 {f : ℝ → ℝ} (hf : f = λ x => (x - 3) / (x - 4)) : {x | f ⁻¹' {x} = ∅} = {1} := by
  -- simplify the expression and goal
  ext x
  constructor
  
  . -- prove that if f⁻¹(x) is empty then x = 1
    intro hx
    simp at hx
    -- if x ≠ 1 then f⁻¹(x) is not empty
    contrapose! hx
    -- simplify hx to x - 1 ≠ 0
    replace hx : x ≠ 1 := by
      simp at hx
      exact hx
    replace hx : x - 1 ≠ 0 := sub_ne_zero_of_ne hx

    -- prove that f ((4 * x - 3) / (x - 1)) = x
    -- introduce y = (4 * x - 3) / (x - 1)
    let y : ℝ := (4 * x - 3) / (x - 1)
    have hy : y = (4 * x - 3) / (x - 1) := by rfl
    -- prove that f y = x
    have hxy : f y = x := by
      -- rewrite and simplify the expression
      rw [hf, hy]
      simp

      -- use two lemmas to simplify the expression
      -- for the numerator
      have h1 : (4 * x - 3) / (x - 1) - 3 = (4 * x - 3 - 3 * (x - 1)) / (x - 1) := by
        calc _ = (4 * x - 3) / (x - 1) + (-3) := by linarith
          _ = (4 * x - 3 + (-3) * (x - 1)) / (x - 1) := div_add' _ _ _ hx
          _ = _ := by ring
      -- for the denominator
      have h2 : (4 * x - 3) / (x - 1) - 4 = (4 * x - 3 - 4 * (x - 1)) / (x - 1) := by
        calc _ = (4 * x - 3) / (x - 1) + (-4) := by linarith
          _ = (4 * x - 3 + (-4) * (x - 1)) / (x - 1) := div_add' _ _ _ hx
          _ = _ := by ring

      -- simplify the expression
      rw [h1, h2]
      -- prove the expression
      conv =>
        lhs
        -- cancel x - 1 in the denominators
        apply div_div_div_cancel_right₀ hx
      ring_nf
    -- prove that y is in f⁻¹(x)
    replace hxy : y ∈ f ⁻¹' {x} := hxy
    -- then f⁻¹(x) is not empty
    exact ⟨y, hxy⟩

  . -- prove that if x = 1 then f⁻¹(x) is empty
    -- simplify the expression
    intro hx
    simp at hx ⊢
    rw[hx]
    -- prove by contradion
    by_contra h
    -- rewrite the expression to have ∃ x, f x = 1
    rw [Set.preimage_singleton_eq_empty] at h
    simp at h
    -- introduce x s.t. f x = 1
    obtain ⟨x, h⟩ := h
    -- then (x - 3) / (x - 4) = 1
    simp [hf] at h
    -- discuss x - 4 = 0 or x - 4 ≠ 0

    by_cases hx0 : x - 4 = 0
    . -- when x - 4 = 0 its trivial
      simp [hx0] at h
    . -- when x - 4 ≠ 0 we have x - 3 = x - 4
      rw [div_eq_one_iff_eq hx0] at h
      -- which is impossible
      linarith
