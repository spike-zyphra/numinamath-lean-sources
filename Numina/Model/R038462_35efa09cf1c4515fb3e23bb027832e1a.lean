import Mathlib

theorem algebra_119952 {a b c : ℝ} (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c)
    (h : ∃ x, a^2 * x + b * c = b^2 * x + a * c ∧ b^2 * x + a * c = c^2 * x + a * b) :
    a + b + c = 0 := by
  rcases h with ⟨x, h1, h2⟩
  have eq1 : (a - b) * ((a + b) * x - c) = 0 := by
    nlinarith
  have h3 : (a + b) * x - c = 0 := by
    apply (mul_right_inj' (show a - b ≠ 0 by
      intro h0
      apply ha
      linarith
    )).mp
    linarith [eq1]
  have eqc : c = (a + b) * x := by
    linarith
  have eq2 : (b - c) * ((b + c) * x - a) = 0 := by
    nlinarith [eqc]
  have h4 : (b + c) * x - a = 0 := by
    apply (mul_right_inj' (show b - c ≠ 0 by
      intro h0
      apply hb
      linarith
    )).mp
    linarith [eq2]
  have eqa : a = (b + c) * x := by
    linarith
  by_cases h7 : 1 + x = 0
  · -- $1 + x = 0$
    have hx : x = -1 := by
      linarith
    rw [hx] at eqc
    have h8 : c = -a - b := by
      nlinarith
    linarith
  · -- $1 + x ≠ 0$
    have h8 : a * (1 - x) = b * x := by
      have eq5 : a - a * x^2 = b * x + b * x^2 := by
        rw [eqc] at eqa
        nlinarith [eqa]
      have eq6 : a * (1 - x^2) = b * x * (1 + x) := by
        nlinarith [eq5]
      have h9 : a * (1 - x) = b * x := by
        apply (mul_left_inj' h7).mp
        linarith [eq6]
      linarith [h9]
    have eq7 : a = x * (a + b) := by
      nlinarith [h8]
    have eq8 : c = x * (a + b) := by
      linarith [eqc]
    have eq9 : a = c := by
      linarith [eq7, eq8]
    contradiction