import Mathlib

theorem algebra_310079 (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) (h : ∑ k, abs (Real.log (x k)) + ∑ k, abs (Real.log (1 / x k)) =
    abs (∑ k, Real.log (x k))) :
    ∀ i, x i = 1 := by
  have h1 : ∀ k : Fin n, abs (Real.log (1 / x k)) = abs (Real.log (x k)) := by
    intro k
    have h2 : Real.log (1 / x k) = - Real.log (x k) := by
      simp [Real.log_div, Real.log_one]
    rw [h2]
    rw [abs_neg]
  have h3 : ∑ k, abs (Real.log (1 / x k)) = ∑ k, abs (Real.log (x k)) := by
    apply Finset.sum_congr
    · rfl
    · intro k hk
      exact h1 k
  rw [h3] at h
  have h4 : ∑ k, abs (Real.log (x k)) ≥ abs (∑ k, Real.log (x k)) := by 
    apply Finset.abs_sum_le_sum_abs
  have h5 : ∑ k, abs (Real.log (x k)) = 0 := by 
    have h6 : abs (∑ k, Real.log (x k)) = 2 * (∑ k, abs (Real.log (x k)) ) := by
      linarith [h]
    have h7 : ∑ k, abs (Real.log (x k)) ≥ abs (∑ k, Real.log (x k)) := by 
      apply Finset.abs_sum_le_sum_abs
    rw [h6] at h7 
    have h8 : ∑ k, abs (Real.log (x k)) ≤ 0 := by
      linarith [h7]
    have h9 : ∑ k, abs (Real.log (x k)) ≥ 0 := by
      apply Finset.sum_nonneg
      intro i hi
      apply abs_nonneg
    linarith
  have h6 : ∀ k : Fin n, abs (Real.log (x k)) = 0 := by 
    intro k
    have hk : abs (Real.log (x k)) ≥ 0 := by apply abs_nonneg
    have h7 : ∑ k, abs (Real.log (x k)) = 0 := h5
    have h8 : abs (Real.log (x k)) = 0 := by 
      have h10 : abs (Real.log (x k)) ≤ ∑ k, abs (Real.log (x k)) := by 
        apply Finset.single_le_sum (fun i hi => abs_nonneg (Real.log (x i))) (by simp)
      rw [h5] at h10
      linarith
    exact h8
  have h7 : ∀ k : Fin n, Real.log (x k) = 0 := by
    intro k
    have h8 : abs (Real.log (x k)) = 0 := h6 k
    rw [abs_eq_zero] at h8 
    exact h8
  intro i
  have h8 : Real.log (x i) = 0 := h7 i
  have h9 : x i = 1 := by
    have hx1 : 0 < x i := hx i 
    rw [Real.log_eq_zero] at h8 
    rcases h8 with (r | r | r)
    · linarith
    · linarith
    · linarith 
  exact h9