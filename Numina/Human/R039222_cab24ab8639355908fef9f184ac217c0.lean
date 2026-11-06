import Mathlib
set_option maxHeartbeats 1000000
open Real

/- ## SUBJECT 3

Let $x, y, z \in \mathbb{R}$ with $x^{4} + y^{4} + z^{4} \leq 48$.

a) Prove that $x^{2} + y^{2} + z^{2} \leq 12$

b) Prove that $\frac{1}{\sqrt{1 + x^{2} + y^{2}}} + \frac{1}{\sqrt{1 + y^{2} + z^{2}}} + \frac{1}{\sqrt{1 + z^{2} + x^{2}}} \geq 1$. In what case do we have equality? prof. Cătălin Zîrnă -/
theorem inequalities_104375 (x y z : ℝ) (h : x^4 + y^4 + z^4 ≤ 48) :
    x^2 + y^2 + z^2 ≤ 12 ∧
    1 ≤ 1 / sqrt (1 + x^2 + y^2) + 1 / sqrt (1 + y^2 + z^2) +
        1 / sqrt (1 + z^2 + x^2) := by
  -- we'll prove this and store result for later
  have h2: x^2+y^2+z^2≤12 := by
    -- just a simple cauchy-schwarz on (x^2, y^2, z^2) and (1, 1, 1)
    let q:∃ v:EuclideanSpace ℝ (Fin 3), v = ![x^2, y^2, z^2] := by
      simp only [exists_eq]
    obtain ⟨v, vdef⟩ := q
    let q:∃ w:EuclideanSpace ℝ (Fin 3), w = ![1, 1, 1] := by
      simp only [exists_eq]
    obtain ⟨w, wdef⟩ := q
    have h' := real_inner_mul_inner_self_le v w
    simp at h'; rw [vdef, wdef] at h';
    rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three] at h';
    simp at h'; ring_nf at h'
    nlinarith
  constructor
  assumption
-- am-gm on √(1 + x^2 + y^2) written as √(3 *(1+x^2 + y^2)/3) is needed
  have hag: ∀ x y:ℝ, √(1+x^2+y^2) ≤ (10+x^2+y^2)/6 := by
    intro x y
    have q:= Real.geom_mean_le_arith_mean2_weighted (w₁:=1/2) (w₂:=1/2) (p₁:=3) (p₂:=(1+x^2+y^2)/3) (by norm_num) (by norm_num) (by linarith) (by nlinarith) (by norm_num)
    norm_num at q
    rw [← Real.mul_rpow (by norm_num) (by nlinarith), mul_div, mul_comm, ←mul_div, div_self (by norm_num), mul_one, ← sqrt_eq_rpow] at q
    linarith
  -- using that on all three terms gives us the answer
  have h1:= hag x y
  have h2:= hag y z
  have h3:= hag z x
  calc 1 / √(1 + x ^ 2 + y ^ 2) + 1 / √(1 + y ^ 2 + z ^ 2) + 1 / √(1 + z ^ 2 + x ^ 2)
  _ ≥ 1 / ((10 + x^2 + y^2)/6) + 1 / ((10 + y^2 + z^2)/6) + 1 / ((10 + z^2 + x^2)/6) := by gcongr
  _ = 6 / (10 + x^2 + y^2) + 6 / (10 + y^2 + z^2) + 6 / (10 + z^2 + x^2) := by rw [one_div_div, one_div_div, one_div_div]
  _ ≥ (√6 + √6 + √6)^2/(10+x^2+y^2+10+y^2+z^2+10+z^2+x^2) := by
    -- another cauchy-schwarz
    have q:∃ v:EuclideanSpace ℝ (Fin 3), v = ![√(6/(10+x^2+y^2)), √(6/(10+y^2+z^2)), √(6/(10+z^2+x^2))] := by
      simp only [exists_eq]
    obtain ⟨v, vdef⟩ := q
    let q:∃ w:EuclideanSpace ℝ (Fin 3), w = ![√(10+x^2+y^2), √(10+y^2+z^2), √(10+z^2+x^2)] := by
      simp only [exists_eq]
    obtain ⟨w, wdef⟩ := q
    have h' := real_inner_mul_inner_self_le v w
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] at h'; rw [vdef, wdef] at h';
    rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three] at h';
    have hxypos: 0 <√(10+x^2+y^2) := by apply Real.sqrt_pos_of_pos; nlinarith
    have hyzpos: 0 <√(10+y^2+z^2) := by apply Real.sqrt_pos_of_pos; nlinarith
    have hzxpos: 0 <√(10+z^2+x^2) := by apply Real.sqrt_pos_of_pos; nlinarith
    simp [
      show √(10 + x ^ 2 + y ^ 2)≠0 by linarith,
      show √(10 + y ^ 2 + z ^ 2)≠0 by linarith,
      show √(10 + z ^ 2 + x ^ 2)≠0 by linarith,
    ] at h'
    rw [show (√6 + √6 + √6) * (√6 + √6 + √6) = (√6 + √6 + √6)^2 by ring_nf] at h'
    conv_rhs at h' =>
      calc _
      _ = (√6^2 / √(10 + x ^ 2 + y ^ 2)^2 + √6^2 / √(10 + y ^ 2 + z ^ 2)^2 + √6^2 / √(10 + z ^ 2 + x ^ 2)^2) * (√(10 + x ^ 2 + y ^ 2)^2 + √(10 + y ^ 2 + z ^ 2)^2 + √(10 + z ^ 2 + x ^ 2)^2) := by ring_nf
      _ = (6 / (10 + x ^ 2 + y ^ 2) + 6 / (10 + y ^ 2 + z ^ 2) + 6 / (10 + z ^ 2 + x ^ 2)) * ((10 + x^2+y^2) + (10+y^2+z^2) + (10+z^2+x^2)) := by rw[sq_sqrt (by norm_num), sq_sqrt (by nlinarith), sq_sqrt (by nlinarith), sq_sqrt (by nlinarith)]
    simp
    have h2:= div_le_div_of_nonneg_right h' (show 0 ≤ (10 + x ^ 2 + y ^ 2 + (10 + y ^ 2 + z ^ 2) + (10 + z ^ 2 + x ^ 2)) by nlinarith)
    rw [← mul_div, div_self (by nlinarith), mul_one, show 10 + x ^ 2 + y ^ 2 + (10 + y ^ 2 + z ^ 2) + (10 + z ^ 2 + x ^ 2)=10 + x ^ 2 + y ^ 2 + 10 + y ^ 2 + z ^ 2 + 10 + z ^ 2 + x ^ 2 by ring_nf] at h2
    assumption
  _ = 54/(30+2*(x^2+y^2+z^2)) := by ring_nf; rw [sq_sqrt (by norm_num)]; ring_nf
  _ ≥ 54/(30+2*12) := by gcongr
  _ = 1 := by norm_num