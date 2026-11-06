import Mathlib

/-What is the coefficient of $x^3$ when $7x^4-3x^3 -3x^2-8x + 1$ is multiplied by $8x^4+2x^3 - 7x^2 + 3x + 4$ and the like terms are combined?-/
theorem algebra_18721 (f g X : Polynomial ℤ) (hX : X = Polynomial.X) (hf : f = 7 * X ^ 4 - 3 * X ^ 3 - 3 * X ^ 2 - 8 * X + 1)
    (hg : g = 8 * X ^ 4 + 2 * X ^ 3 - 7 * X ^ 2 + 3 * X + 4) :
    (f * g).coeff 3 = 37 := by
  -- expand the expression of (f * g).coeff 3
  rw [Polynomial.coeff_mul]
  -- enumerate the Finset.antidiagonal 3
  have eq : Finset.antidiagonal 3 = {(3, 0), (2, 1), (1, 2), (0, 3)} := by
    ext x
    simp
    apply Iff.intro <;> intro h
    -- when x.1 + x.2 = 3
    . set y := x.1 with hy
      match y with
      | 0 => -- when y = 0
        right; right; right
        -- show that x.2 = 3
        ring_nf at h
        calc
          x = (x.1, x.2) := by rfl
          _ = (0, 3) := by rw [<-hy, h]
      | 1 => -- when y = 1
        right; right; left
        -- show that x.2 = 2
        replace h : x.2 = 2 := by linarith only [h]
        calc
          x = (x.1, x.2) := by rfl
          _ = (1, 2) := by rw [h, hy]
      | 2 => -- when y = 2
        right; left
        -- show that x.2 = 1
        replace h : x.2 = 1 := by linarith only [h]
        calc
          x = (x.1, x.2) := by rfl
          _ = (2, 1) := by rw [h, hy]
      | 3 => -- when y = 3
        left
        -- show that x.2 = 0
        replace h : x.2 = 0 := by linarith only [h]
        calc
          x = (x.1, x.2) := by rfl
          _ = (3, 0) := by rw [h, hy]
      | z + 4 => -- when y ≥ 4
        have ineq : 4 ≤ z + 4 + x.2 := by linarith
        rw [h] at ineq
        contradiction
    -- when x ∈ {(0, 3), (1, 2), (2, 1), (3, 0)}
    . rcases h with h | h | h | h
      all_goals rw [h]; norm_num
  -- simplify the desired equation
  rw [eq]
  simp [Finset.sum]
  rw [hf, hg, hX]
  ring_nf
  -- show that Polynomial.coeff 1 n = 0 when n ≠ 0
  have const (n : ℕ) (hn : n ≠ 0) : Polynomial.coeff (1 : Polynomial ℤ) n = 0 := by
    apply Polynomial.coeff_C_ne_zero
    exact hn
  have const1 := const 1 (show 1 ≠ 0 by norm_num)
  have const2 := const 2 (show 2 ≠ 0 by norm_num)
  have const3 := const 3 (show 3 ≠ 0 by norm_num)
  norm_num [const1, const2, const3] -- rewrite the equation, so that we can get the answer
  have (n : ℕ) : (Polynomial.C (4 : ℤ)).coeff n = Polynomial.coeff 4 n := by rfl
  simp only [Polynomial.coeff_X, ← this, Polynomial.coeff_C]
  norm_num
