import Mathlib

theorem algebra_291492 (n : ℕ) (hn : n > 0) (a : Fin n → ℝ)
    (hsum : ∑ i : Fin n, a i = -1.5) (hnewsum : ∑ i : Fin n, (a i - 2) = -15.5) :
    n = 7 := by 
  have eq1 : ∑ i : Fin n, (a i - 2) = ∑ i : Fin n, a i - ∑ i : Fin n, (2 : ℝ) := by 
    rw [Finset.sum_sub_distrib]
  have eq2 : ∑ i : Fin n, (2 : ℝ) = (n : ℝ) * 2 := by 
    simp [Finset.sum_const, Finset.card_univ]
    <;> ring
  rw [eq1, eq2] at hnewsum
  rw [hsum] at hnewsum
  norm_num at hnewsum ⊢
  have hn' : (n : ℝ) = 7 := by 
    nlinarith
  have h_n : n = 7 := by
    exact_mod_cast hn'
  exact h_n