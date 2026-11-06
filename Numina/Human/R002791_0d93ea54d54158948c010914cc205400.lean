import Mathlib

open Real Set
open scoped BigOperators

/- Example 3 Given non-negative real numbers $x, y, z, w$ satisfy $x^{2}+y^{2}+z^{2}+w^{2}+x+2 y+3 z+4 w=\frac{17}{2}$, try to find the maximum and minimum values of $x+$ $y+z+w$.

 untranslated part:
将上面的文本翻译成英文，请保留源文本的换行和格式，直接输出翻译结果。

Since the last part is a note about the translation instruction, it is not part of the text to be translated. Here is the translation of the provided text:

Example 3 Given non-negative real numbers $x, y, z, w$ satisfy $x^{2}+y^{2}+z^{2}+w^{2}+x+2 y+3 z+4 w=\frac{17}{2}$, try to find the maximum and minimum values of $x+$ $y+z+w$. -/
theorem algebra_113912
  (S:Set ℝ) (hS : S = {s | ∃ x y z w :ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ 0 ≤ w ∧ x^2 + y^2 + z^2 + w^2 + x + 2 * y + 3 * z + 4 * w = 17/2 ∧ s = x + y + z + w}) :
  IsLeast S (-2+5*√2/2) ∧ IsGreatest S 3 := by
  rw [hS]; clear hS S
  constructor
  rotate_left
  · conv =>
      lhs; rhs; intro s; rhs; intro x; rhs; intro y; rhs; intro z; rhs; intro w
      rhs; rhs; rhs; rhs; rw [show x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 + x + 2 * y + 3 * z + 4 * w = (x+1/2)^2+(y+1)^2+(z+3/2)^2+(w+2)^2-15/2 by ring_nf]

    unfold IsGreatest upperBounds; simp only [exists_and_left, mem_setOf_eq, forall_exists_index, and_imp]
    constructor
    rotate_left
    · intro lim x hx y hy z hz w hw h hlim
      rw [hlim]; clear hlim lim
      -- let a = x+1/2, b = y+1, c = z+3/2, d = w+2
      let q:∃ a:ℝ, a = x+1/2 := by
        simp only [exists_eq]
      obtain ⟨a, adef⟩ := q
      let q:∃ b:ℝ, b = y+1 := by
        simp only [exists_eq]
      obtain ⟨b, bdef⟩ := q
      let q:∃ c:ℝ, c = z+3/2 := by
        simp only [exists_eq]
      obtain ⟨c, cdef⟩ := q
      let q:∃ d:ℝ, d = w+2 := by
        simp only [exists_eq]
      obtain ⟨d, ddef⟩ := q
      rw [← adef, ← bdef, ← cdef, ← ddef] at h
      apply congr_arg (fun t => t + 15/2) at h; norm_num at h
      suffices a+b+c+d≤ 8 by linarith
      -- cauchy schwarz gives the result
      have h1: (a+b+c+d)^2 ≤ 8^2 := by
        let q:∃ v:EuclideanSpace ℝ (Fin 4), v = ![a, b, c, d] := by
          simp only [exists_eq]
        obtain ⟨v, vdef⟩ := q
        let q:∃ w:EuclideanSpace ℝ (Fin 4), w = ![1, 1, 1, 1] := by
          simp only [exists_eq]
        obtain ⟨w, wdef⟩ := q
        have h' := real_inner_mul_inner_self_le v w
        simp at h'; rw [vdef, wdef] at h';
        rw [Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four] at h';
        simp at h'; norm_num at h'
        rw [show (a+b+c+d)*(a+b+c+d)= (a+b+c+d)^2 by ring_nf, show a*a+b*b+c*c+d*d=a^2+b^2+c^2+d^2 by ring_nf, h] at h'
        norm_num at h' ⊢; assumption
      nlinarith
    · -- from the proof it's clear we get least value if we set each inner term to 2
      use 3/2; constructor; norm_num
      use 1; constructor; norm_num
      use 1/2; constructor; norm_num
      use 0; constructor; norm_num
      norm_num
  · unfold IsLeast lowerBounds; simp only [exists_and_left, mem_setOf_eq, forall_exists_index, and_imp]
    constructor
    rotate_left
    · intro lim x hx y hy z hz w hw h hlim
      rw [hlim]; clear hlim lim
      have h0:=
        calc (x+y+z+w)^2 + 4*(x+y+z+w)
        _ ≥ x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 + x + 2 * y + 3 * z + 4 * w := by nlinarith
        _ = 17/2 := by rw [h]
      -- let S = x+y+z+w
      let q:∃ S:ℝ, S = x+y+z+w := by
        simp only [exists_eq]
      obtain ⟨S, Sdef⟩ := q
      rw [← Sdef] at h0 ⊢
      have h1: (S+2)^2 ≥ 17/2+4 := by nlinarith
      have h2: 25/2 ≤ (S+2)^2 := by linarith
      have h3: (5*√2/2)^2 ≤ (S+2)^2 := by ring_nf; rw [Real.sq_sqrt (by norm_num)]; norm_num; linarith
      apply sq_le_sq.mp at h3
      rw [abs_of_nonneg (by positivity)] at h3
      apply le_abs'.mp at h3
      cases' h3 with h3 h3
      · have h4:0 ≤ 5 * √2 / 2 := by positivity
        have h5:S+2 ≤ 0 := by linarith
        exfalso; linarith
      · linarith
    · -- to reach the goal we use x, y, z, w = (0, 0, 0, -2+5*√2/2)
      use 0; constructor; norm_num
      use 0; constructor; norm_num
      use 0; constructor; norm_num
      use -2+5*√2/2; constructor; norm_num; suffices 4/5 ≤ √2 by linarith
      refine (le_sqrt' ?_).mpr ?_; norm_num; norm_num
      norm_num; ring_nf; rw [Real.sq_sqrt (by norm_num)]; norm_num