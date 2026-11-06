import Mathlib

/- Given that $a$ and $b$ are two roots of the equation $x^{2}+x-3=0$, then the value of $ab-2023a-2023b$ is ______. -/
theorem algebra_8983 {a b : ℝ} (ha : a^2 + a - 3 = 0) (hb : b^2 + b - 3 = 0)(hab: a ≠ b) : a * b - 2023 * a - 2023 * b = 2020 := by
have hdis: discrim (1:ℝ) 1 (-3) = √13 * √13 := by
  rw [discrim]
  simp [norm_num]
  ring
have ha1: a = (-1+√13)/(2*1) ∨ a = (-1-√13)/(2*1) := by
  have ht1: (1:ℝ) ≠ 0 := by norm_num
  have ht2: 1 * (a * a) + 1 * a + -3 = 0 := by
    rw [← ha]; ring
  apply (quadratic_eq_zero_iff ht1 hdis a).mp ht2
have hb1: b = (-1+√13)/(2*1) ∨ b = (-1-√13)/(2*1) := by
  have ht1: (1:ℝ) ≠ 0 := by norm_num
  have ht2: 1 * (b * b) + 1 * b + -3 = 0 := by
    rw [← hb]; ring
  apply (quadratic_eq_zero_iff ht1 hdis b).mp ht2
-- by vieta theorem, if x1, x2 are two roots of the equation ax^2+bx+c=0, then x1+x2=-b/a and x1x2=c/a
have vieta_theorem_add: a+b = -1 := by
  rcases ha1 with haleft | haright
  rcases hb1 with hbleft | hbright
  rw [haleft, hbleft] at hab
  contradiction
  rw [haleft,hbright]
  ring
  rcases hb1 with hbleft | hbright
  rw [haright, hbleft]
  ring
  rw [haright, hbright] at hab
  contradiction
have vieta_theorem_mul: a*b = -3 := by
  have ht1: (-1 + √13) / (2 * 1) * ((-1 - √13) / (2 * 1)) = -3 := by
    have: √13 ^ 2 = 13 := by simp
    ring_nf
    rw [this]
    ring
  have ht2: (-1 - √13) / (2 * 1) * ((-1 + √13) / (2 * 1)) = -3 := by
    rw [← ht1]
    ring
  rcases ha1 with haleft | haright
  rcases hb1 with hbleft | hbright
  rw [haleft, hbleft] at hab
  contradiction
  rw [haleft, hbright]
  exact ht1
  rcases hb1 with hbleft | hbright
  rw [haright, hbleft]
  exact ht2
  rw [haright, hbright] at hab
  contradiction
have h1: a * b - 2023 * a - 2023 * b = (a*b) - 2023*(a+b) := by ring
rw [h1, vieta_theorem_add, vieta_theorem_mul]
ring
