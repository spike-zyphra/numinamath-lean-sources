import Mathlib

open Real Set
open scoped BigOperators

/- 9.208. $\sqrt{x^{2}-9 x+20} \leq \sqrt{x-1} \leq \sqrt{x^{2}-13}$.

Translate the above text into English, please retain the original text's line breaks and format, and output the translation result directly.

9.208. $\sqrt{x^{2}-9 x+20} \leq \sqrt{x-1} \leq \sqrt{x^{2}-13}$. -/
theorem inequalities_171327 (x : ℝ) (sqrtValid: 0≤ x^2-9*x+20) (sqrtValid2: 0≤ x-1) (sqrtValid3: 0≤ x^2-13) :
  (sqrt (x^2 - 9 * x + 20) ≤ sqrt (x - 1)) ∧
  (sqrt (x - 1) ≤ sqrt (x^2 - 13)) ↔ x ∈ Icc 5 7 ∪ {4} := by
  -- let's first determine where the square roots are valid
  simp at sqrtValid2
  rw [show x^2-13 = (x-√13)*(x+√13) by ring_nf; rw [Real.sq_sqrt (by norm_num)]; ring_nf] at sqrtValid3
  apply mul_nonneg_iff.mp at sqrtValid3
  -- right side is clearly not possible due to sqrtValid2
  cases' sqrtValid3 with sqrtValid3 sqrtValid4
  rotate_left; exfalso; linarith
  -- one branch is useless, also removes sqrtValid2
  apply And.left at sqrtValid3; simp at sqrtValid3; clear sqrtValid2
  rw [show x ^ 2 - 9 * x + 20 = (x - 5) * (x - 4) by ring_nf] at sqrtValid
  apply mul_nonneg_iff.mp at sqrtValid
  -- we can sligtly simplify this
  have s2: 5 ≤ x ∨ x ≤ 4 := by
    cases' sqrtValid with sqrtValid sqrtValid
    left; linarith
    right; linarith
  clear sqrtValid
  -- lean doesn't like sqrt 13
  have s1:3 < x := by
    suffices 3 < √13 by linarith
    exact lt_sqrt_of_sq_lt (by norm_num)
  -- now we can start solving the problem
  constructor
  · rintro ⟨hl, hr⟩; simp
    -- square both eqns.
    apply (Real.sqrt_le_sqrt_iff (by linarith)).mp at hl
    apply (Real.sqrt_le_sqrt_iff' (by linarith)).mp at hr
    have hl': 0 ≤ -x ^ 2 + 10 * x - 21 := by linarith
    have hr': 0 ≤ x ^ 2 - x - 12 := by linarith
    rw [show -x^2 + 10 * x - 21 = -(x - 7) * (x - 3) by ring_nf] at hl'
    rw [show x^2 - x - 12 = (x-4)*(x+3) by ring_nf] at hr'
    -- we can determine when the product is positive
    apply mul_nonneg_iff.mp at hl'
    apply mul_nonneg_iff.mp at hr'
    simp at hl' hr'
    -- right branch of hl' is impossible
    cases' hl' with hl' hl'
    rotate_left; exfalso; linarith
    -- hr' simplifies
    have hrs:4 ≤ x ∨ x ≤ -3 := by
      cases' hr' with hr' hr'
      left; linarith
      right; linarith
    clear hr'
    -- and we can eliminate the useless branch
    cases' hrs with hrs hrs
    rotate_left; exfalso; linarith
    clear hl hr s1 sqrtValid3
    -- right branch of hl' is also useless
    apply And.left at hl'
    -- now the problem is trivial
    cases' s2 with s2 s2
    right; constructor <;> linarith
    left; linarith
  · --result verification is simple
    intro h; simp at h
    cases' h with h h
    rw [h]; norm_num
    constructor
    · apply (Real.sqrt_le_sqrt_iff (by linarith)).mpr
      suffices 0 ≤ -x ^ 2 + 10 * x - 21 by linarith
      rw [show -x^2 + 10 * x - 21 = -(x - 7) * (x - 3) by ring_nf]
      apply mul_nonneg_iff.mpr
      simp
      left
      constructor <;> linarith
    · apply (Real.sqrt_le_sqrt_iff' (by linarith)).mpr
      suffices 0 ≤ x ^ 2 - x - 12 by linarith
      rw [show x^2 - x - 12 = (x-4)*(x+3) by ring_nf]
      apply mul_nonneg_iff.mpr
      simp
      left
      constructor <;> linarith