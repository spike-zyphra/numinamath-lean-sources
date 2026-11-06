import Mathlib

/- Let $0 < \alpha < 1$. Consider the sequence $(a_n)_{n \ge 1}$ defined by:
\[
\begin{cases} 
a_1 = 1 + \alpha \\ 
(\forall n \ge 1) \hspace{2mm} : \hspace{2mm} a_{n+1} = \dfrac{1}{a_n} + \alpha 
\end{cases}
\]
Prove that $a_n > 1$ for all $n \ge 1$. -/
theorem algebra_2467 (α : ℝ) (hα : α ∈ Set.Ioo 0 1) {a : ℕ → ℝ} (ha1 : a 1 = 1 + α) (han : ∀ n ≥ 1, a (n + 1) = 1 / a n + α) : ∀ n ≥ 1, a n > 1 := by
  
  simp_all
  obtain ⟨po, l1⟩ := hα

  have lem : ∀ m, 1 < a (m + 1) ∧ a (m+1) <1/(1-α) := by

    have ine: 1+α  < 1/(1-α) := by 
      have t1: (1+α) * (1-α) < 1 := by nlinarith
      have t2: @Inv.inv ℝ DivInvMonoid.toInv (1 - α) * (1-α) = 1 := by 
        field_simp; 
        refine (div_eq_one_iff_eq ?_).mpr rfl
        linarith
      nth_rw 3 [←t2] at t1
      simp
      nlinarith

    intro m
    induction' m with m hm

    simp [ha1]
    constructor
    exact po
    simp at ine
    assumption
    
    obtain ⟨hml,hmu⟩ := hm
    have : a (m+1 + 1) = (a (m+1))⁻¹ + α := by 
      apply han (m+1)
      linarith
    rw [this]

    have : 1-α < @Inv.inv ℝ Real.instInv (a (m + 1)) := by 
      field_simp
      refine (lt_one_div ?_ ?_).mp hmu
      linarith
      linarith
    have : @Inv.inv ℝ Real.instInv (a (m + 1)) < 1 := by
      field_simp
      refine Bound.div_lt_one_of_pos_of_lt ?_ hml
      linarith

    constructor
    linarith
    linarith

  intro n hn
  have : ∃ m:ℕ, m + 1 = n := by use (n-1); omega
  obtain ⟨m, hm⟩ := this
  have : 1 < a (m + 1) ∧ a (m + 1) < 1 / (1 - α) := by apply lem
  rw [hm] at this
  exact this.left