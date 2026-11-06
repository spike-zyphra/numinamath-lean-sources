import Mathlib

theorem algebra_7882 {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hdist : a ≠ b ∧ a ≠ c ∧ b ≠ c) (hroots : ∃ x, a * x ^ 2 + b * x + c = 0 ∧ b * x ^ 2 + a * x + c = 0) :
    a + b + c = 0 := by
  rcases hroots with ⟨x, hx₁, hx₂⟩
  have hab : (a - b) * (x^2 - x) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp hab) with h1 h2
  · -- Case where $a - b = 0$, which would mean $a = b$
    exfalso
    apply hdist.left
    linarith
  · -- Case where $x^2 - x = 0$
    have hx2x : x * (x - 1) = 0 := by
      ring_nf at h2 ⊢
      linarith
    cases' (mul_eq_zero.mp hx2x) with hx0 hx1
    · -- Case where $x = 0$
      exfalso
      have hc' : c = 0 := by
        rw [show x = 0 by linarith] at hx₁
        nlinarith
      contradiction
    · -- Case where $x - 1 = 0$, so $x = 1$
      have hx1' : x = 1 := by linarith
      rw [show x = 1 by linarith] at hx₁
      linarith
  all_goals omega
  all_goals tauto
  all_goals nlinarith