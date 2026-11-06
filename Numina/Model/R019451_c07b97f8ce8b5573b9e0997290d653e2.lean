import Mathlib

theorem algebra_226167 (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (h1 : (a * b, b * c, c * d, d * a) = (a, b, c, d)) :
    a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 := by
  have h2 : a * b = a := by
    exact congrArg (λ w => w.1) h1
  -- solving from the second component
  have h3 : b * c = b := by
    exact congrArg (λ w => w.2.1) h1
  -- solving from the third component
  have h4 : c * d = c := by
    exact congrArg (λ w => w.2.2.1) h1
  -- solving from the fourth component
  have h5 : d * a = d := by
    exact congrArg (λ w => w.2.2.2) h1
  -- From h2: a * b = a, factoring gives a(b - 1) = 0. Since a ≠ 0, we get b = 1.
  have hb1 : b = 1 := by
    apply (mul_left_inj' ha).mp
    linarith
  -- From h3: b * c = b, factoring gives b(c - 1) = 0. Since b ≠ 0, we get c = 1.
  have hc1 : c = 1 := by
    apply (mul_left_inj' hb).mp
    linarith
  -- From h4: c * d = c, factoring gives c(d - 1) = 0. Since c ≠ 0, we get d = 1.
  have hd1 : d = 1 := by
    apply (mul_left_inj' hc).mp
    linarith
  -- From h5: d * a = d, factoring gives d(a - 1) = 0. Since d ≠ 0, we get a = 1.
  have ha1 : a = 1 := by
    apply (mul_left_inj' hd).mp
    linarith
  exact ⟨ha1, hb1, hc1, hd1⟩