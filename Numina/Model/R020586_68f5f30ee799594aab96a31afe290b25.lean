import Mathlib

theorem algebra_35927 {a b c d : ℝ} (ha : a ≠ b) (hb : a ≠ c) (hc : a ≠ d)
    (hd : b ≠ c) (he : b ≠ d) (hf : c ≠ d) (hroots : {x | x^2 - 2 * c * x - 5 * d = 0} = {a, b})
    (hroots' : {x | x^2 - 2 * a * x - 5 * b = 0} = {c, d}) :
    a + b + c + d = 30 := by
  have h1 : a ^ 2 - 2 * c * a - 5 * d = 0 := by
    have h4 : a ∈ {x | x ^ 2 - 2 * c * x - 5 * d = 0} := by
      rw [hroots]
      simp
    simpa using h4
  have h2 : b ^ 2 - 2 * c * b - 5 * d = 0 := by
    have h5 : b ∈ {x | x ^ 2 - 2 * c * x - 5 * d = 0} := by
      rw [hroots]
      simp
    simpa using h5
  have h3 : c ^ 2 - 2 * a * c - 5 * b = 0 := by
    have h6 : c ∈ {x | x ^ 2 - 2 * a * x - 5 * b = 0} := by
      rw [hroots']
      simp
    simpa using h6
  have h4 : d ^ 2 - 2 * a * d - 5 * b = 0 := by
    have h7 : d ∈ {x | x ^ 2 - 2 * a * x - 5 * b = 0} := by
      rw [hroots']
      simp
    simpa using h7
  have eq1 : a + b = 2 * c := by
    have h5 : (a - b) * (a + b - 2 * c) = 0 := by
      nlinarith
    have h6 : a - b ≠ 0 := by
      intro h
      apply ha
      linarith
    have h7 : a + b - 2 * c = 0 := by
      apply (mul_eq_zero.mp h5).resolve_left
      exact h6
    linarith
  have eq2 : c + d = 2 * a := by
    have h10 : (c - d) * (c + d - 2 * a) = 0 := by
      nlinarith
    have h11 : c - d ≠ 0 := by
      intro h
      apply hf
      linarith
    have h12 : c + d - 2 * a = 0 := by
      apply (mul_eq_zero.mp h10).resolve_left
      exact h11
    linarith
  -- Now, we need to show $a + c = 15$.
  have eq3 : a + c = 15 := by
    have eq5 : b = 2 * c - a := by
      linarith [eq1]
    have eq6 : d = 2 * a - c := by
      linarith [eq2]
    rw [eq5] at h2
    rw [eq6] at h4
    -- Now, we need to show `(a - c) * (a + c - 15) = 0`.
    have h5 : (a - c) * (a + c - 15) = 0 := by
      nlinarith [sq_pos_of_ne_zero (show (a - c) ≠ 0 by intro h; apply hb; linarith)]
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- Case $a - c = 0$, which means $a = c$, contradiction
      exfalso
      apply hb
      linarith
    · -- Case $a + c - 15 = 0$
      linarith
  -- Finally, sum all the equations.
  have eq4 : a + b + c + d = 30 := by
    nlinarith [eq1, eq2, eq3]
  linarith [eq4]