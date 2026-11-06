import Mathlib

theorem algebra_188479 (n : ℕ) (hn : n > 0) (a : Fin n → ℝ)
    (hsum : ∑ i : Fin n, a i = 40) (hrepl : ∑ i : Fin n, (1 - a i) = 20) :
    ∑ i : Fin n, (1 + a i) = 100 := by
  have h₁ : ∑ i : Fin n, (1 - a i) = ∑ i : Fin n, 1 - ∑ i : Fin n, a i := by
    rw [Finset.sum_sub_distrib]
    <;> simp
  rw [h₁] at hrepl 
  have h₂ : (n : ℝ ) = 60 := by
    have h3 : (∑ i : Fin n, (1 : ℝ)) = 60 := by
      linarith [hsum, hrepl]
    have hn' : (∑ i : Fin n, (1 : ℝ)) = (n : ℝ) := by
      simp [Finset.sum_const, Finset.card_univ]
      <;> ring
    rw [hn'] at h3
    linarith
  have h₃ : ∑ i : Fin n, (1 + a i) = ∑ i : Fin n, 1 + ∑ i : Fin n, a i := by
    rw [Finset.sum_add_distrib]
    all_goals simp
  rw [h₃]
  have hn' : (∑ i : Fin n, (1 : ℝ)) = (n : ℝ) := by
    simp [Finset.sum_const, Finset.card_univ]
    <;> ring
  rw [hn', hsum]
  have nROKE : (n : ℝ) = 60 := h₂
  rw [nROKE]
  all_goals norm_num