import Mathlib

/-Find all the solutions to
\[3 \sqrt[3]{3x - 2} = x^3 + 2.\]Enter all the solutions, separated by commas.-/
theorem algebra_20320 :
    {x | ∃y, y ^ 3 = 3 * x - 2 ∧ 3 * y = x ^ 3 + 2} = {1, -2} := by
  ext x
  simp
  -- divide into two parts
  apply Iff.intro <;> intro h
  -- show that x = 1 or x = -2
  . obtain ⟨y, hy, hx⟩ := h
    replace hx : x ^ 3 = 3 * y - 2 := by linarith only [hx]
    -- subtract two sides of the equation
    have eq : x ^ 3 - y ^ 3 = 3 * y - 3 * x := by
      linarith only [hx, hy]
    -- factorize the equation
    replace eq : (x - y) * (x ^ 2 + x * y + y ^ 2 + 3) = 0 := by
      ring_nf at eq ⊢
      linarith only [eq]
    -- show that x = y or x ^ 2 + x * y + y ^ 2 + 3 > 0
    have pos1 : x ^ 2 + x * y + y ^ 2 + (3 : ℝ) > 0 := by
      calc
        x ^ 2 + x * y + y ^ 2 + 3 = (x + y / 2) ^ 2 + 3 / (4 : ℝ) * y ^ 2 + 3 := by ring_nf
        _ ≥ 3 := by nlinarith
        _ > 0 := by norm_num
    zify at pos1
    -- have x = y or x ^ 2 + x * y + y ^ 2 + 3 = 0
    rw [mul_eq_zero] at eq
    cases eq with
    -- when x ^ 2 + x * y + y ^ 2 + 3 = 0
    | inr eq =>norm_cast at pos1 eq; linarith only [pos1, eq] -- contradiction
    -- when x = y
    | inl eq =>
      replace eq : x = y := by linarith only [eq]
      rw [<-eq] at hx
      -- substitute y with x, and factorize the equation
      replace hx : x ^ 3 - 3 * x + 2 = 0 := by linarith only [hx]
      replace hx : (x - 1) ^ 2 * (x + 2) = 0 := by ring_nf at hx ⊢; exact hx
      -- show that x = 1 or x = -2
      rw [mul_eq_zero] at hx
      cases hx with
      -- when x + 2 = 0
      | inr hx => 
        right
        linarith only [hx]
      -- when (x - 1) ^ 2 = 0
      | inl hx =>
        left
        nlinarith only [hx] 
  -- show that x = 1 or x = -2 is the solution
  . cases h with
    -- when x = 1
    | inl hx =>
      rw [hx]
      norm_num
    -- when x = -2
    | inr hx =>
      rw [hx]
      norm_num
      use -2
      norm_num