import Mathlib
open Real
/- Given that all terms of the sequence $\left\{ {{a}_{n}} \right\}$ are non-zero real numbers, and for any positive integer $n$, we have ${{\left( {{a}_{1}}+{{a}_{2}}+\cdots +{{a}_{n}} \right)}^{2}}=a_{1}^{3}+a_{2}^{3}+\cdots +a_{n}^{3}$.

When $n=3$, find all sequences of three terms ${{a}_{1}}$, ${{a}_{2}}$, ${{a}_{2}}$ that satisfy the condition.-/
theorem algebra_633616
  (a : ℕ → ℝ)
  (h₀ : ∀ n, a n ≠ 0)
  (h₁ : ∀ n, (∑ i in Finset.Icc 1 n, a i) ^ 2 = ∑ i in Finset.Icc 1 n, (a i) ^ 3)
  : (a 1 = 1 ∧ a 2 = 2 ∧ a 3 = 3) ∨ (a 1 = 1 ∧ a 2 = 2 ∧ a 3 = -2) ∨ (a 1 = 1 ∧ a 2 = -1 ∧ a 3 = 1) := by

  have h1 := h₁ 1
  simp [Finset.sum_Icc_succ_top] at h1
  have ha1 : a 1 = 1 := by
    have h : a 1 ^ 2 = a 1 ^ 3 := by linarith
    have h' : a 1 ^ 2 * (1 - a 1) = 0 := by linarith
    have h'' : a 1 ^ 2 = 0 ∨ 1 - a 1 = 0 := by
      apply mul_eq_zero.1 h'
    rcases h'' with h''' | h''''
    · -- $a_1 ^ 2 = 0$ is impossible because $a_1 \neq 0$
      exfalso
      exact h₀ 1 (by
        rw [sq_eq_zero_iff] at h'''
        exact h''')
    · -- $1 - a_1 = 0$ implies that $a_1 = 1$.
      linarith

  have h2 := h₁ 2
  simp [Finset.sum_Icc_succ_top, ha1] at h2
  have p2 : (a 2 - 2) * (a 2 + 1) * a 2 = 0 := by
    ring_nf at h2 ⊢
    nlinarith [h₀ 1, h₀ 2]
  have : a 2 = 2 ∨ a 2 = -1 := by
    rcases mul_eq_zero.1 p2 with h | h
    · rcases mul_eq_zero.1 h with h' | h'
      · left; linarith
      · right; linarith
    · -- $a_2 = 0$ is impossible because $a_2 \neq 0$.
      exfalso; exact h₀ 2 h

  rcases this with ha2 | ha2
  · -- Case $a_2 = 2$:
    have h3 := h₁ 3
    simp [Finset.sum_Icc_succ_top, ha1, ha2] at h3
    have p3 : (a 3 - 3) * (a 3 + 2) * a 3 = 0 := by
      ring_nf at h3 ⊢
      nlinarith [h₀ 1, h₀ 2, h₀ 3]
    have : a 3 = 3 ∨ a 3 = -2 := by
      rcases mul_eq_zero.1 p3 with h | h
      · rcases mul_eq_zero.1 h with h' | h'
        · left; linarith
        · right; linarith
      · -- $a_3 = 0$ is impossible because $a_3 \neq 0$.
        exfalso; exact h₀ 3 h

    rcases this with ha3 | ha3
    · left
      exact ⟨ha1, ha2, ha3⟩
    · right
      left
      exact ⟨ha1, ha2, by linarith⟩

  · -- Case $a_2 = -1$:
    have h3 := h₁ 3
    simp [Finset.sum_Icc_succ_top, ha1, ha2] at h3
    have p3 : a 3 ^ 2 * (a 3 - 1) = 0 := by
      ring_nf at h3 ⊢
      nlinarith [h₀ 1, h₀ 2, h₀ 3]
    have : a 3 = 1 := by
      rcases mul_eq_zero.1 p3 with h | h
      · -- $a_3 ^ 2 = 0$ is impossible because $a_1 \neq 0$.
        exfalso
        exact h₀ 3 (by
          rw [sq_eq_zero_iff] at h
          exact h)
      · linarith

    right
    right
    exact ⟨ha1, ha2, this⟩
  