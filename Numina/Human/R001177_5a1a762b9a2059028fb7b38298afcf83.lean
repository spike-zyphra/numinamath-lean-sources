import Mathlib

/-Each solution to $x^2 + 5x + 8 = 0$ can be written in the form $x = a + b i,$ where $a$ and $b$ are real numbers. What is $a + b^2$?-/
theorem algebra_20883 {x : ℂ} (hx : x^2 + 5 * x + 8 = 0) :
    x.1 + x.2 ^ 2 = -3 / 4 := by
  -- simplify the hx to (x + 5 / 2) ^ 2 + 7 / 4 = 0
  replace hx : (x + 5 / 2) ^ 2 + 7 / 4 = 0 := by
    ring_nf at hx ⊢
    exact hx
  -- easy to check that -7 / 4 is square of √7 / 2 * Complex.I
  have eqI : (√7 / 2 * Complex.I) ^ 2 = -7 / 4 := by
    ring_nf
    norm_num
    norm_cast
    rw [Real.sq_sqrt]
    norm_cast
    norm_num
    norm_num
  -- convert hx to (x + 5 / 2) ^ 2 = -7 / 4
  replace hx : (x + 5 / 2) ^ 2 = -7 / 4 := by 
    calc
      (x + 5 / 2) ^ 2 = (x + 5 / 2) ^ 2 + 7 / 4 - 7 / 4 := by ring_nf
      _ = 0 - 7 / 4 := by rw [hx]
      _ = -7 / 4 := by ring_nf
  -- cancel the square, so that we get the solution of x
  rw [<-eqI] at hx
  apply eq_or_eq_neg_of_sq_eq_sq at hx
  -- by two solution of x, we have x.1 = -5 / 2 and x.2 ^ 2 = 7 / 4
  replace hx : x.1 = -5 / 2 ∧ x.2 ^ 2 = 7 / 4 := by
    cases hx with
    -- when x = -5 / 2 + √7 / 2 * Complex.I
    | inr hx =>
      rw [Complex.ext_iff] at hx
      norm_num at hx
      refine ⟨?_, ?_⟩
      -- show that x.1 = -5 / 2
      . linarith only [hx]
      -- show that x.2 ^ 2 = 7 / 4 
      . obtain ⟨_, hxim⟩ := hx
        rw [hxim]
        ring_nf
        rw [Real.sq_sqrt]
        ring_nf
        norm_num
    -- when x = -5 / 2 - √7 / 2 * Complex.I, same as above
    | inl hx =>
      rw [Complex.ext_iff] at hx
      norm_num at hx
      refine ⟨?_, ?_⟩
      -- show that x.1 = -5 / 2
      . linarith only [hx]
      -- show that x.2 ^ 2 = 7 / 4
      . obtain ⟨_, hxim⟩ := hx
        rw [hxim]
        ring_nf
        rw [Real.sq_sqrt]
        ring_nf
        norm_num
  -- finally the answer is easy to get
  linarith only [hx]