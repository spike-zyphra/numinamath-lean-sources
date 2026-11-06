import Mathlib

theorem algebra_254260 (A B C : ℤ) (h : ∀ n : ℕ, ∑ i in Finset.Icc 1 n, (i / (2 ^ i : ℚ)) = (A * n + B) / (2 ^ n : ℚ) + C) :
    A = -1 ∧ B = -2 ∧ C = 2 := by
  have eq1 := h 0
  norm_num [Finset.sum_eq_zero] at eq1
  have eq2 := h 1
  norm_num [Finset.sum_Icc_succ_top] at eq2
  have eq3 := h 2
  norm_num [Finset.sum_Icc_succ_top] at eq3
  have h1 : (A : ℚ) = -1 := by
    linarith
  have h2 : (B : ℚ) = -2 := by
    linarith
  have h3 : (C : ℚ) = 2 := by
    linarith
  have h1' : A = -1 := by
    exact_mod_cast h1
  have h2' : B = -2 := by
    exact_mod_cast h2
  have h3' : C = 2 := by
    exact_mod_cast h3
  exact ⟨h1', h2', h3'⟩