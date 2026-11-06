import Mathlib

theorem algebra_189004 {a : ℕ → ℝ} (ha : ∀ n, a n = 1 + 3 / 2 * n * (n - 1))
    (h : ∀ n, a (n + 1) - a n = 3 / 2 * n) :
    ∀ n, a n = 1 + 3 / 2 * n * (n - 1) ∧
    ∑ i in Finset.range n, a i = 1 / 2 * n * (n ^ 2 + 1) := by
  intro n
  constructor
  · -- Show that the formula for the $n$-th term is correct
    exact ha n 
  · -- Show that the sum of the first n terms is correct

    -- First establishing that the hypotheses about `a` are inconsistent 
    have eq1 := h 1
    have eq2 := h 0
    -- From h 0: a1 -a 0 =0 
    have eq3 : a 1 = a 0 := by
      norm_num at eq2 ⊢ 
      linarith 
    -- From ha 0 and ha 1:
    have eq4 : a 0 = 1 := by 
      specialize ha 0 
      norm_num at ha ⊢ 
      linarith 
    have eq5 : a 1 = 1 := by 
      have eq5 : a 1 = a 0 := eq3 
      rw [eq5] 
      linarith [eq4] 
    -- From h 1: a 2 -a 1 =3/2, so a 2 = a1+3/2
    have eq6 : a 2 = (a 1 : ℝ) + 3 / 2 := by
      have eq6 := h 1 
      norm_num at eq6 ⊢ 
      linarith 
    -- From ha 2:
    have eq7 : a 2 = 4 := by 
      specialize ha 2 
      norm_num at ha ⊢ 
      linarith 
    -- Substituting a1: 
    have eq8 : (4 : ℝ) = (5 / 2 : ℝ) := by 
      rw [eq5] at eq6 
      linarith [eq6, eq7] 
    -- This leads to a contradiction 
    -- From this inconsistency, any statement is derivable 
    exfalso 
    linarith