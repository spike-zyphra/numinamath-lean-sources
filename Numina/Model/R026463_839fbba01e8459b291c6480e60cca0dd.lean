import Mathlib

theorem algebra_40602 (a b c : ℝ) (ha : a^3-3*a+1=0) (hb : b^3-3*b+1=0)
    (hc : c^3-3*c+1=0) (hdist : a≠b ∧ a≠c ∧ b≠c) :
    a^8+b^8+c^8=186 := by
  have ha3 : a^3 = 3*a - 1 := by linarith
  have hb3 : b^3 = 3*b - 1 := by linarith
  have hc3 : c^3 = 3*c - 1 := by linarith
  have ha4 : a^4 = 3*a^2 - a := by
    calc
      a^4 = a * a^3 := by ring
      _   = a * (3*a - 1) := by rw [ha3]
      _   = 3*a^2 - a := by ring
  have hb4 : b^4 = 3*b^2 - b := by
    calc
      b^4 = b * b^3 := by ring
      _   = b * (3*b - 1) := by rw [hb3]
      _   = 3*b^2 - b := by ring
  have hc4 : c^4 = 3*c^2 - c := by
    calc
      c^4 = c * c^3 := by ring
      _   = c * (3*c - 1) := by rw [hc3]
      _   = 3*c^2 - c := by ring
  have ha8 : a^8 = 28*a^2 - 27*a + 6 := by
    calc
      a^8 = (a^4)^2 := by ring
      _ = (3*a^2 - a)^2 := by rw [ha4]
      _ = 9*a^4 - 6*a^3 + a^2 := by ring
      _ = 9*(3*a^2 - a) - 6*(3*a - 1) + a^2 := by rw [ha4, ha3]
      _ = 28*a^2 - 27*a + 6 := by ring
  have hb8 : b^8 = 28*b^2 - 27*b + 6 := by
    calc
      b^8 = (b^4)^2 := by ring
      _ = (3*b^2 - b)^2 := by rw [hb4]
      _ = 9*b^4 - 6*b^3 + b^2 := by ring
      _ = 9*(3*b^2 - b) - 6*(3*b - 1) + b^2 := by rw [hb4, hb3]
      _ = 28*b^2 - 27*b + 6 := by ring
  have hc8 : c^8 = 28*c^2 - 27*c + 6 := by
    calc
      c^8 = (c^4)^2 := by ring
      _ = (3*c^2 - c)^2 := by rw [hc4]
      _ = 9*c^4 - 6*c^3 + c^2 := by ring
      _ = 9*(3*c^2 - c) - 6*(3*c - 1) + c^2 := by rw [hc4, hc3]
      _ = 28*c^2 - 27*c + 6 := by ring
  have hab : a^2 + a*b + b^2 = 3 := by
    have h1 : a^3 - 3*a + 1 = 0 := ha
    have h2 : b^3 - 3*b + 1 = 0 := hb
    have h3 : a^3 - b^3 - 3*(a - b) = 0 := by linarith
    have h4 : (a - b) * (a^2 + a*b + b^2 - 3) = 0 := by
      ring_nf at h3 ⊢
      linarith
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- Case $a - b = 0$, which implies $a = b$, a contradiction.
      exfalso
      apply hdist.left
      linarith
    · -- Case $a^2 + a*b + b^2 - 3 = 0$.
      linarith
  have hac : a^2 + a*c + c^2 = 3 := by
    have h1 : a^3 - 3*a + 1 = 0 := ha
    have h2 : c^3 - 3*c + 1 = 0 := hc
    have h3 : a^3 - c^3 - 3*(a - c) = 0 := by linarith
    have h4 : (a - c) * (a^2 + a*c + c^2 - 3) = 0 := by
      ring_nf at h3 ⊢
      linarith
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- Case $a - c = 0$, which implies $a = c$, a contradiction.
      exfalso
      apply hdist.right.left
      linarith
    · -- Case $a^2 + a*c + c^2 - 3 = 0$.
      linarith
  have hbc : b^2 + b*c + c^2 = 3 := by
    have h1 : b^3 - 3*b + 1 = 0 := hb
    have h2 : c^3 - 3*c + 1 = 0 := hc
    have h3 : b^3 - c^3 - 3*(b - c) = 0 := by linarith
    have h4 : (b - c) * (b^2 + b*c + c^2 - 3) = 0 := by
      ring_nf at h3 ⊢
      linarith
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- Case $b - c = 0$, which implies $b = c$, a contradiction.
      exfalso
      apply hdist.right.right
      linarith
    · -- Case $b^2 + b*c + c^2 - 3 = 0$.
      linarith
  have hsum : a + b + c = 0 := by
    have eq1 : (b - c) * (a + b + c) = 0 := by
      nlinarith [hab, hac]
    cases' (mul_eq_zero.mp eq1) with h5 h6
    · -- Case $b - c = 0$, which implies $b = c$, a contradiction.
      exfalso
      apply hdist.right.right
      linarith
    · -- Case $a + b + c = 0$.
      linarith
  have hsq : a^2 + b^2 + c^2 = 6 := by
    nlinarith [hsum, hab, hac, hbc]
  nlinarith [ha8, hb8, hc8, hsum, hsq]