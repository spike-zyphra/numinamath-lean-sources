import Mathlib

set_option maxHeartbeats 400000
/-Let f and g be two quadratic polynomials with real coefficients such that
the equation f(g(x))=0 has four distinct real solutions 112 131 146 and a.
Compute the sum of all possible values of a-/
theorem algebra_610795: ∑ᶠ a ∈ {a: ℝ | (a ≠ 112) ∧ (a ≠ 131) ∧ (a ≠ 146) ∧
 (∃ r s q t: ℝ, ∀ x: ℝ, ((x ^ 2 + q * x + t - r) * (x ^ 2 + q * x + t - s) = 0 ↔
x = 112 ∨ x = 131 ∨ x = 146 ∨ x = a))}, a = 389 := by
  -- we may assume that f and g are monic, hence here we write f = (x-r)(x-s) and g = x^2 + q*x + t

  -- we directly compute all the possible values of a
  have set_eq: {a: ℝ | (a ≠ 112) ∧ (a ≠ 131) ∧ (a ≠ 146) ∧
 (∃ r s q t: ℝ, ∀ x: ℝ, ((x ^ 2 + q * x + t - r) * (x ^ 2 + q * x + t - s) = 0 ↔
x = 112 ∨ x = 131 ∨ x = 146 ∨ x = a))} = {97, 127, 165} := by
    ext a
    constructor
    -- the first direction
    . intro h
      simp only [Set.mem_setOf_eq] at h
      rcases h with ⟨h1, h2, h3, h⟩
      obtain ⟨r, s, q, t, h4⟩ := h
      have f1:= h4 112
      have f2:= h4 131
      have f3:= h4 146
      have f4:= h4 a
      simp at f1 f2 f3 f4
      -- then we check all cases for the permutation of roots
      rcases f1 with f1 | f1
      -- f1.1
      . rcases f2 with f2 | f2
        . have hq: q = - 243 := by nlinarith
          rw [hq] at f1 f2 f3 f4
          rcases f3 with f3 | f3
          . nlinarith
          . rcases f4 with f4 | f4
            . have f: a ^ 2 - 131 ^ 2 + 243 * (131 - a) = 0 := by nlinarith
              replace f: (a - 131) * (a + 131 - 243) = 0 := by nlinarith
              simp at f
              rcases f with f | f
              . absurd h2
                linarith
              . replace f: a = 112 := by linarith
                absurd h1
                rw [f]
            . have f: a ^ 2 - 146 ^ 2 + 243 * (146 - a) = 0 := by nlinarith
              replace f: (a - 146) * (a + 146 - 243) = 0 := by nlinarith
              simp at f
              rcases f with f | f
              . absurd h3
                linarith
              . replace f: a = 97 := by linarith
                simp [f]
        . rcases f3 with f3 | f3
          . have hq: q = - 258 := by nlinarith
            rw [hq] at f1 f2 f3 f4
            rcases f4 with f4 | f4
            . have f: a ^ 2 - 146 ^ 2 + 258 * (146 - a) = 0 := by nlinarith
              replace f: (a - 146) * (a + 146 - 258) = 0 := by nlinarith
              simp at f
              rcases f with f | f
              . absurd h3
                linarith
              . replace f: a = 112 := by linarith
                absurd h1
                rw [f]
            . have f: a ^ 2 - 131 ^ 2 + 258 * (131 - a) = 0 := by nlinarith
              replace f: (a - 131) * (a + 131 - 258) = 0 := by nlinarith
              simp at f
              rcases f with f | f
              . absurd h2
                linarith
              . replace f: a = 127 := by linarith
                simp [f]
          . have hq: q = - 277 := by nlinarith
            rw [hq] at f1 f2 f3 f4
            rcases f4 with f4 | f4
            . have f: a ^ 2 - 112 ^ 2 + 277 * (112 - a) = 0 := by nlinarith
              replace f: (a - 112) * (a + 112 - 277) = 0 := by nlinarith
              simp at f
              rcases f with f | f
              . absurd h1
                linarith
              . replace f: a = 165 := by linarith
                simp [f]
            . have f: a ^ 2 - 146 ^ 2 + 277 * (146 - a) = 0 := by nlinarith
              replace f: (a - 146) * (a + 146 - 277) = 0 := by nlinarith
              simp at f
              rcases f with f | f
              . absurd h3
                linarith
              . replace f: a = 131 := by linarith
                absurd h2
                linarith
      -- f1.2, similar as above
      . rcases f2 with f2 | f2
        . rcases f3 with f3 | f3
          . have hq: q = - 277 := by nlinarith
            rw [hq] at f1 f2 f3 f4
            rcases f4 with f4 | f4
            . have f: a ^ 2 - 146 ^ 2 + 277 * (146 - a) = 0 := by nlinarith
              replace f: (a - 146) * (a + 146 - 277) = 0 := by nlinarith
              simp at f
              rcases f with f | f
              . absurd h3
                linarith
              . replace f: a = 131 := by linarith
                absurd h2
                rw [f]
            . have f: a ^ 2 - 112 ^ 2 + 277 * (112 - a) = 0 := by nlinarith
              replace f: (a - 112) * (a + 112 - 277) = 0 := by nlinarith
              simp at f
              rcases f with f | f
              . absurd h1
                linarith
              . replace f: a = 165 := by linarith
                simp [f]
          . have hq: q = - 258 := by nlinarith
            rw [hq] at f1 f2 f3 f4
            rcases f4 with f4 | f4
            . have f: a ^ 2 - 131 ^ 2 + 258 * (131 - a) = 0 := by nlinarith
              replace f: (a - 131) * (a + 131 - 258) = 0 := by nlinarith
              simp at f
              rcases f with f | f
              . absurd h2
                linarith
              . replace f: a = 127 := by linarith
                simp [f]
            . have f: a ^ 2 - 146 ^ 2 + 258 * (146 - a) = 0 := by nlinarith
              replace f: (a - 146) * (a + 146 - 258) = 0 := by nlinarith
              simp at f
              rcases f with f | f
              . replace f: a = 146 := by linarith
                absurd h3
                rw [f]
              . replace f: a = 112 := by linarith
                absurd h1
                linarith
        . have hq: q = - 243 := by nlinarith
          rw [hq] at f1 f2 f3 f4
          rcases f3 with f3 | f3
          . rcases f4 with f4 | f4
            . have f: a ^ 2 - 146 ^ 2 + 243 * (146 - a) = 0 := by nlinarith
              replace f: (a - 146) * (a + 146 - 243) = 0 := by nlinarith
              simp at f
              rcases f with f | f
              . absurd h3
                linarith
              . replace f: a = 97 := by linarith
                simp [f]
            . have f: a ^ 2 - 112 ^ 2 + 243 * (112 - a) = 0 := by nlinarith
              replace f: (a - 112) * (a + 112 - 243) = 0 := by nlinarith
              simp at f
              rcases f with f | f
              . absurd h1
                linarith
              . replace f: a = 131 := by linarith
                absurd h2
                linarith
          . rcases f4 with f4 | f4
            . have f: a ^ 2 - 131 ^ 2 + 243 * (131 - a) = 0 := by nlinarith
              replace f: (a - 131) * (a + 131 - 243) = 0 := by nlinarith
              simp at f
              rcases f with f | f
              . absurd h2
                linarith
              . replace f: a = 112 := by linarith
                absurd h1
                rw [f]
            . have f: a ^ 2 - 146 ^ 2 + 243 * (146 - a) = 0 := by nlinarith
              replace f: (a - 146) * (a + 146 - 243) = 0 := by nlinarith
              simp at f
              rcases f with f | f
              . absurd h3
                linarith
              . replace f: a = 97 := by linarith
                simp [f]

    -- the second direction
    . intro h
      simp at h
      rcases h with h | h | h
      all_goals simp [h]
      -- a = 97
      . use -146 * 97
        use -112 * 131
        use -243
        use 0
        intro x
        constructor
        . rw [show x ^ 2 + -243 * x + 0 - -146 * 97 = (x - 146) * (x - 97) by ring]
          rw [show x ^ 2 + -243 * x + 0 - -112 * 131 = (x - 112) * (x - 131) by ring]
          intro hx
          rcases hx with hx | hx
          all_goals simp at hx
          . rcases hx with hx | hx
            . replace hx: x = 146 := by linarith
              rw [hx]
              norm_num
            . replace hx: x = 97 := by linarith
              rw [hx]
              norm_num
          . rcases hx with hx | hx
            . replace hx: x = 112 := by linarith
              rw [hx]
              norm_num
            . replace hx: x = 131 := by linarith
              rw [hx]
              norm_num
        . intro hx
          rcases hx with hx | hx | hx | hx
          all_goals simp [hx]; norm_num
      -- a = 127
      . use -146 * 112
        use -127 * 131
        use -258
        use 0
        intro x
        constructor
        . rw [show x ^ 2 + -258 * x + 0 - -146 * 112 = (x - 146) * (x - 112) by ring]
          rw [show x ^ 2 + -258 * x + 0 - -127 * 131 = (x - 127) * (x - 131) by ring]
          intro hx
          rcases hx with hx | hx
          all_goals simp at hx
          . rcases hx with hx | hx
            . replace hx: x = 146 := by linarith
              rw [hx]
              norm_num
            . replace hx: x = 112 := by linarith
              rw [hx]
              norm_num
          . rcases hx with hx | hx
            . replace hx: x = 127 := by linarith
              rw [hx]
              norm_num
            . replace hx: x = 131 := by linarith
              rw [hx]
              norm_num
        . intro hx
          rcases hx with hx | hx | hx | hx
          all_goals simp [hx]; norm_num
      -- a = 165
      . use -165 * 112
        use -131 * 146
        use -277
        use 0
        intro x
        constructor
        . rw [show x ^ 2 + -277 * x + 0 - -165 * 112 = (x - 165) * (x - 112) by ring]
          rw [show x ^ 2 + -277 * x + 0 - -131 * 146 = (x - 131) * (x - 146) by ring]
          intro hx
          rcases hx with hx | hx
          all_goals simp at hx
          . rcases hx with hx | hx
            . replace hx: x = 165 := by linarith
              rw [hx]
              norm_num
            . replace hx: x = 112 := by linarith
              rw [hx]
              norm_num
          . rcases hx with hx | hx
            . replace hx: x = 131 := by linarith
              rw [hx]
              norm_num
            . replace hx: x = 146 := by linarith
              rw [hx]
              norm_num
        . intro hx
          rcases hx with hx | hx | hx | hx
          all_goals simp [hx]; norm_num


  -- then we compute the finsum
  rw [set_eq]
  clear *-
  rw [finsum_mem_eq_finite_toFinset_sum]
  simp
  norm_num
  apply Set.toFinite