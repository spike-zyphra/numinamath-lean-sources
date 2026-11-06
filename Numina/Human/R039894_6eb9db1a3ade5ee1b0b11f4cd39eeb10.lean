import Mathlib

/- 3. Solve the equation


$$

\sqrt{\frac{x-2}{11}}+\sqrt{\frac{x-3}{10}}+\sqrt{\frac{x-4}{9}}=\sqrt{\frac{x-11}{2}}+\sqrt{\frac{x-10}{3}}+\sqrt{\frac{x-9}{4}}

$$
 -/
theorem algebra_178182 (x : ℝ) (hx : x ≥ 2 ∧ x ≥ 3 ∧ x ≥ 4 ∧ x ≥ 11 ∧ x ≥ 10 ∧ x ≥ 9 ∧ x ≥ 1) :
    Real.sqrt ((x - 2) / 11) + Real.sqrt ((x - 3) / 10) + Real.sqrt ((x - 4) / 9) =
    Real.sqrt ((x - 11) / 2) + Real.sqrt ((x - 10) / 3) + Real.sqrt ((x - 9) / 4) ↔ x = 13 := by
    constructor
    rotate_left
    · -- verify first, easy part
      intro hx'
      rw [hx']; norm_num
    -- let x=t+13
    let q:∃ t:ℝ, x = t+13 := by
      use x-13; simp
    obtain ⟨t, tdef⟩ := q
    rw [tdef]
    intro h; simp
    norm_num at h
    rw [show t+13-2=t+11 by ring_nf, show t+13-3=t+10 by ring_nf, show t+13-4=t+9 by ring_nf, show t+13-11=t+2 by ring_nf, show t+13-10=t+3 by ring_nf, show t+13-9=t+4 by ring_nf, ← Real.sqrt_div (by linarith), ← Real.sqrt_div (by linarith), ← Real.sqrt_div (by linarith), ← Real.sqrt_div (by linarith), ← Real.sqrt_div (by linarith), ← Real.sqrt_div (by linarith)] at h
    -- we need to analyze depending on sign of t
    cases' lt_trichotomy t 0 with hlt hep
    rotate_left
    cases' hep with heq hgt
    · -- t=0 is trivial given the goal
      assumption
    · -- t>0, we'll go by contradiction
      exfalso
      -- idea: right side is larger than left
      suffices √((t + 11) / 11) + √((t + 10) / 10) + √((t + 9) / 9) < √((t + 2) / 2) + √((t + 3) / 3) + √((t + 4) / 4) by linarith
      gcongr ?_ + ?_ + ?_
      apply Real.sqrt_lt_sqrt (by linarith); linarith
      apply Real.sqrt_lt_sqrt (by linarith); linarith
      apply Real.sqrt_lt_sqrt (by linarith); linarith
    · --last option, t<0, then left side is larger than right
      suffices √((t + 2) / 2) + √((t + 3) / 3) + √((t + 4) / 4) < √((t + 11) / 11) + √((t + 10) / 10) + √((t + 9) / 9) by linarith
      gcongr ?_ + ?_ + ?_
      apply Real.sqrt_lt_sqrt (by linarith); linarith
      apply Real.sqrt_lt_sqrt (by linarith); linarith
      apply Real.sqrt_lt_sqrt (by linarith); linarith