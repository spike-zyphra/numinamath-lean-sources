import Mathlib
open Mathlib
/--
The set of all real numbers $x$ for which
\[\log_{2004}(\log_{2003}(\log_{2002}(\log_{2001}{x})))\]
is defined is $\{x\mid x > c\}$. What is the value of $c$?
$\textbf {(A) } 0\qquad \textbf {(B) }2001^{2002} \qquad \textbf {(C) }2002^{2003} \qquad \textbf {(D) }2003^{2004} \qquad \textbf {(E) }2001^{2002^{2003}}$
-/
lemma algebra_1150 (c : ℝ) (h : ∀ x, 0 < x ∧ 0 < Real.logb 2001 x ∧ 0 < Real.logb 2002 (Real.logb 2001 x) ∧ 0 < Real.logb 2003 (Real.logb 2002 (Real.logb 2001 x)) ↔ c < x) : c = 2001^(2002 : ℝ) := by
  -- For all real numbers $a,b,$ and $c$ such that $b>1,$ note that:
  -- $\log_b a$ is defined if and only if $a>0.$ $\log_b a>c$ if and only if $a>b^c.$

  have mass1 : ∀ x, (0 < x ∧ 0 < Real.logb 2001 x ∧ 0 < Real.logb 2002 (Real.logb 2001 x) ∧ 0 < Real.logb 2003 (Real.logb 2002 (Real.logb 2001 x))) ↔ (1 < x ∧ 1 < Real.logb 2001 x ∧ 1 < Real.logb 2002 (Real.logb 2001 x)) := by
    intro x
    constructor
    · intro d
      rcases d with ⟨d1, ⟨d2, ⟨d3, d4⟩⟩⟩
      have a1 : 1 < x := by
        rw [Real.logb_pos_iff (by norm_num : (1 : ℝ) < 2001) d1] at d2
        exact d2
      have a2 : 1 < Real.logb 2001 x := by
        rw [Real.logb_pos_iff (by norm_num : (1 : ℝ) < 2002) d2] at d3
        exact d3
      have a3 : 1 < Real.logb 2002 (Real.logb 2001 x) := by
        rw [Real.logb_pos_iff (by norm_num : (1 : ℝ) < 2003) d3] at d4
        exact d4
      tauto
    · intro d
      rcases d with ⟨d1, ⟨d2, d3⟩⟩
      constructor <;> try linarith
      constructor <;> try linarith
      constructor <;> try linarith
      rw [←Real.logb_pos_iff (by norm_num : (1 : ℝ) < 2003)] at d3
      exact d3
      linarith
  simp_rw [mass1] at h
  clear mass1
  -- Therefore, we have \begin{align*} \log_{2004}(\log_{2003}(\log_{2002}(\log_{2001}{x}))) \text{ is defined} &\implies \log_{2003}(\log_{2002}(\log_{2001}{x}))>0 \\ &\implies \log_{2002}(\log_{2001}{x})>1 \\ &\implies \log_{2001}{x}>2002 \\ &\implies x>2001^{2002}, \end{align*} from which $c=\boxed{\textbf {(B) }2001^{2002}}.$
  have mass2 : ∀ x, 1 < x ∧ 1 < Real.logb 2001 x ∧ 1 < Real.logb 2002 (Real.logb 2001 x) ↔ 2001^(2002 : ℝ) < x := by
    intro x
    constructor <;> intro d
    · rcases d with ⟨d1, ⟨d2, d3⟩⟩
      rw [Real.lt_logb_iff_rpow_lt (by norm_num : (1 : ℝ) < 2001) (by linarith)] at d2
      rw [Real.lt_logb_iff_rpow_lt (by norm_num : (1 : ℝ) < 2002), Real.lt_logb_iff_rpow_lt (by norm_num : (1 : ℝ) < 2001) (by linarith)] at d3
      rw [(by norm_num : 2002 ^ (1 : ℝ) = (2002 : ℝ))] at d3
      exact d3
      · rw [←Real.logb_pos_iff (by norm_num : (1 : ℝ) < 2001)] at d1
        exact d1
        linarith
    · have a1 : 1 < x := by linarith
      have a2 : 1 < Real.logb 2001 x := by
        rw [Real.lt_logb_iff_rpow_lt (by norm_num : (1 : ℝ) < 2001) (by linarith)]
        linarith
      have a3 : 1 < Real.logb 2002 (Real.logb 2001 x) := by
        rw [Real.lt_logb_iff_rpow_lt (by norm_num : (1 : ℝ) < 2002) (by linarith)]
        rw [Real.lt_logb_iff_rpow_lt (by norm_num : (1 : ℝ) < 2001) (by linarith)]
        rw [(by norm_num : 2002 ^ (1 : ℝ) = (2002 : ℝ))]
        exact d
      tauto
  simp_rw [mass2] at h
  clear mass2
  cases' lt_trichotomy c (2001^(2002 : ℝ)) with h1 h1
  · have := (h _).2 h1
    linarith
  cases' h1 with h1 h1
  · exact h1
  · have := (h _).1 h1
    linarith