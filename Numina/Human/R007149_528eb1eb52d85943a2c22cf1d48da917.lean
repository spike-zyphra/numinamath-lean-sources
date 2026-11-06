import Mathlib

/-Let $a, b, c$ be complex numbers, with $a$ real, such that \[a+b+c=ab+bc+ca=abc=3.\]Find $a$.-/
theorem algebra_11325 {a b c : ℂ} (ha : a.im = 0) (h1 : a + b + c = 3) (h2 : a * b + b * c + c * a = 3)
    (h3 : a * b * c = 3) : a = 1 + 2 ^ ((1 : ℂ) / 3) := by
  --By Vieta's formulas, $a, b, c$ are the roots of the polynomial \[x^3 - 3x^2 + 3x - 3 = 0.\]Adding $2$ to both sides, we can factor this equation as \[(x-1)^3 = 2.\]For the real value $x = a$, we have $a - 1 = \sqrt[3]{2}$, so $a = \boxed{1 + \sqrt[3]{2}}$.
  have eq : ∀x, (x - a) * (x - b) * (x - c) =
          x^3 - (a + b + c) * x^2 + (a * b + b * c + c * a) *x - a * b * c := by
      intro x
      ring_nf
  rw [h1, h2, h3] at eq
  have : (a - 1)^3 = (a^3 - 3 * a^2 + 3 * a - 3) + 2 := by ring_nf
  have p : (a - 1)^3 = 2 := by
    rw [this, (eq a).symm, sub_self]
    simp

  -- Although a = 1 + 2^(1/3) is obvious, but, it is difficult to prove it.
  rw [Complex.cpow_def]
  have ha' : a.re = a := by
    exact Complex.ext rfl (id (Eq.symm ha))
  -- split `if` of cpow
  split
  . -- if 2 = 0, which is impossible
    rename_i h
    absurd h
    simp
  . -- 2 ≠ 0
    -- replace `2` to `a - 1`, and expand log
    rw [p.symm, Complex.log]
    -- prove ((a - 1) ^ 3).arg is 0
    have : ((a - 1) ^ 3).arg = 0 := by
      rw [p]
      simp
    rw [this]
    field_simp
    rw [Complex.abs_eq_sqrt_sq_add_sq]
    have : (a - 1).im = 0 := by
      rw [Complex.sub_im, Complex.one_im, ha]
      simp
    rw [this]
    simp
    norm_cast

    -- this part is condition of `sqrt_sq` and `exp_log`
    have : (a.re - 1) ^ 3 = (2 : ℂ) := by
      rw [p.symm]
      rw [ha']
    norm_cast at this
    have : (a.re - 1) ^ 3 > 0 := by linarith
    have : 0 < a.re - 1 := by
      have h : Odd 3 := by norm_cast
      apply (Odd.pow_pos_iff h).mp
      linarith

    -- now, we need to prove a = ↑(1 + Real.exp (Real.log √((a.re - 1) ^ 2)))
    rw [Real.sqrt_sq this.le, Real.exp_log this]
    simp
    exact ha'.symm