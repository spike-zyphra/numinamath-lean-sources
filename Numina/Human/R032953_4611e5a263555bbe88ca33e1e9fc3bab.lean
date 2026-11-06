import Mathlib

/- The difference of the roots of the quadratic equation $x^2 + bx + c = 0$
is $|b - 2c|$. If $c \neq 0$, then find $c$ in terms of $b$. -/
theorem algebra_19412 {b c : ℝ}(hc : c ≠ 0)
  (hroots : ∃ x y, x ≠ y ∧
  x^2 + b * x + c = 0 ∧ y^2 + b * y + c = 0 ∧
  |x - y| = |b - 2*c|): c = b - 1 := by
  rcases hroots with ⟨x,y,hxy⟩
  have eqx: 1 * (x*x) + b*x + c = 0 := by
    rw [← hxy.right.left]; ring
  have eqy: 1 * (y*y) + b*y + c = 0 := by
    rw [← hxy.right.right.left]; ring
  -- the equation has solution, so discriminant ≥ 0, can be written in a square form
  let s := 2*x+b
  have s_def: s = 2*x+b := rfl
  have discsq: discrim 1 b c = s*s := by
    have hh1: (1:ℝ) ≠ 0 := by norm_num
    rw [(quadratic_eq_zero_iff_discrim_eq_sq hh1 x).mp eqx]
    rw [s_def]; ring
  have s_def': |s| = √(b^2-4*c) := by
    have: b^2-4*c = s^2 := by
      rw [pow_two s, ← discsq]
      rw [discrim]
      ring
    rw [this]
    symm
    exact Real.sqrt_sq_eq_abs s
  -- solve the equation
  have eqroot(z:ℝ): 1*(z*z)+b*z+c=0 →
    (z = -b/2 + s/2 ∨ z = -b/2 -s/2) := by
    intro heq
    have hh1: (1:ℝ) ≠ 0 := by norm_num
    have hh2 := (quadratic_eq_zero_iff hh1 discsq z).mp heq
    rcases hh2 with hh2 | hh2
    <;> rw [hh2] <;> ring_nf <;> simp
  -- so their difference is s
  have difxy: |x-y| = |s| := by
    have hh1 := eqroot x eqx
    have hh2 := eqroot y eqy
    have xny := hxy.left
    rcases hh1 with hx1 | hx2
    · rcases hh2 with hy1 | hy2
      · rw [hx1, hy1] at xny
        simp at xny
      · rw [hx1, hy2]; simp
    · rcases hh2 with hy1 | hy2
      · have: x-y = -s := by
          rw [hx2, hy1]
          ring
        rw [this]
        simp
      · rw [hx2, hy2] at xny
        simp at xny
  -- then we get equations of b and c
  have eqbc': |b-2*c| = √(b^2-4*c) := by
    rw [← hxy.right.right.right]
    rw [difxy, s_def']
  -- square eqbc;, 4c(c-b+1)=0
  have eqbc: (4*c)*(c-b+1) = 0 := by
    have hh1: b^2-4*b*c+4*c^2 - (b^2-4*c) = 0 := by
      have tt1: b^2-4*c = (√(b^2-4*c))^2 := by
        have: 0 ≤ b^2-4*c := by
          have: b^2-4*c = discrim 1 b c := by
            rw [discrim]; ring
          rw [this, discsq, ← pow_two]
          apply sq_nonneg
        exact Eq.symm (Real.sq_sqrt this)
      have tt2: |b-2*c|^2 = (b-2*c)^2 := by simp
      rw [tt1, ← eqbc', tt2]; ring
    rw [← hh1]; ring
  -- because c ≠ 0, we have c-b+1 = 0. or c = b-1
  have hbc := mul_eq_zero.mp eqbc
  rcases hbc with hbc1 | hbc2
  · simp at hbc1; contradiction
  · linarith [hbc2]
