import Mathlib

theorem algebra_300072 {f: ℝ → ℝ} {a b c p1 p2 m1 m2 : ℝ} (ha : a > b) (hb : b > c)
  (hf: ∀x:ℝ, f x = a*x^2+b*x+c)
  (hf2: f 2 = 0) (hfm1: f m1 = p1)(hfm2: f m2 = p2)
  (h1: p1*p2 - c*p1 + a*p2 - a*c = 0):
  f (m1 + 5) > 0 ∨ f (m2 + 5) > 0 := by
  have hf2': 4*a + 2*b + c = 0 := by
    rw [← hf2, hf 2]
    ring
  have apos: 0 < a := by
    linarith [hf2', ha, hb]
  have cneg: c < 0 := by
    linarith [hf2', ha, hb]
  have hf': ∀x, f x = a * (x*x - (-b/a)*x + c/a) := by
    intro x;  rw [hf x]
    field_simp [apos.ne']
    ring
  have h2: ∃k, (∀x, f x = a * (x - 2) * (x - k)) ∧
    b = -a*(2+k) ∧ c = 2*k*a := by
    -- 2 is a root of a(x^2-(-b/a)x+c) = 0, or, root of x^2 - (-b/a)x + c = 0
    have: 2*2 - (-b/a)*2 + c/a = 0 := by
      rw [hf' 2] at hf2
      simp only [mul_eq_zero, apos.ne', false_or] at hf2
      exact hf2
    rcases (vieta_formula_quadratic this) with ⟨k, heq, hbk, hck⟩
    use k
    replace hbk: b = -a*(2+k) := by
      rw [hbk]
      field_simp [apos.ne']
    replace hck: c = 2*k * a := by
      rw [hck]
      field_simp [apos.ne']
    refine ⟨?_, hbk, hck⟩
    intro x
    rw [hf x, hbk, hck]
    ring
  rcases h2 with ⟨k, hfk, hbk, hck⟩
  have kgt: k > -3 := by
    have: a*1 > a*(-(2+k)) := by
      linarith [ha, hbk]
    replace: 1 > -(2+k) := (mul_lt_mul_left apos).mp this
    linarith [this]
  have kneg: k < 0 := by
    rw [hck] at cneg
    nlinarith [cneg, apos]
  have: (p1+a)*(p2-c) = 0 := by
    rw [← h1]
    ring
  rcases (mul_eq_zero.mp this) with hp1 | hp2
  · -- p1+a = 0 case.
    replace: (m1-2)*(m1-k) < 0 := by
      have: a*(m1-2)*(m1-k) < 0 := by
        rw [← hfk m1, hfm1]
        linarith [hp1, apos]
      rw [mul_assoc] at this
      exact (pos_iff_neg_of_mul_neg this).mp apos
    have hm1: k < m1 ∧ m1 < 2 := by
      rw [mul_neg_iff] at this
      rcases this with hh | hh
      · -- impossible for m1 > 2 but < k.
        exfalso; linarith [hh, kneg]
      · constructor
        all_goals linarith [hh]
    left
    rw [hfk (m1+5)]
    have h2: m1+5-2 > 0 := by
      linarith [hm1.left]
    have h3: m1+5-k > 0 := by
      linarith [hm1.left]
    apply mul_pos ?_ h3
    apply mul_pos apos h2
  · -- p2-c=0 case.
    have h2: m2 * (a*m2 + b) = 0 := by
      rw [hf m2] at hfm2
      nlinarith [hfm2, hp2]
    have hm2: m2 = 0 ∨ m2 = 2+k := by
      rcases (mul_eq_zero.mp h2) with hh | hh
      · left; exact hh
      · right
        rw [hbk] at hh
        nlinarith [hh, apos.ne']
    right
    suffices m2+5 > 2  by
      rw [hfk (m2+5)]
      rw [mul_assoc]
      apply mul_pos apos ?_
      apply mul_pos (by linarith [this]) ?_
      linarith [this, kneg]
    rcases hm2 with hm2 | hm2
    all_goals linarith [hm2, kneg]