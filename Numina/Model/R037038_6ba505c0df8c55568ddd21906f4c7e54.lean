import Mathlib


open Real Set


theorem algebra_9470 {f : ℝ → ℝ} (hf : f = λ x => logb 2 (2 * x - x ^ 2)) (a b : ℝ) (h : a < b) (hdomain : ∀ x ∈ Set.Ioo a b, 2 * x - x ^ 2 > 0) :
    MonotoneOn f (Set.Ioo a b) ↔ (Set.Ioo a b) ⊆ Set.Ioo 0 1 := by
  constructor
  · -- Forward direction: if $f$ is monotone on $(a,b)$, then $(a,b) \subseteq (0,1)$
    intro hmono
    intro x hx
    have hx1 : a < x := hx.1
    have hx2 : x < b := hx.2
    have hx3 : 0 < x := by
      have h1 : 2 * x - x ^ 2 > 0 := hdomain x ⟨hx1, hx2⟩
      nlinarith
    have hx4 : x < 2 := by
      have h1 : 2 * x - x ^ 2 > 0 := hdomain x ⟨hx1, hx2⟩
      nlinarith
    have hx5 : x < 1 := by
      by_contra h6
      push_neg at h6
      have hx6 : 1 ≤ x := by nlinarith
      -- Now, we pick our specific points for the contradiction.
      have h7 : a < b := by linarith
      have hy1 : a < x + (b - x)/2 := by
        nlinarith
      have hy2 : x + (b - x)/2 < b := by
        nlinarith
      have hy_in : (x + (b - x)/2) ∈ Set.Ioo a b := ⟨by
          nlinarith
        , by
          nlinarith
      ⟩
      have hy3 : 2 * (x + (b - x)/2) - (x + (b - x)/2) ^ 2 > 0 := hdomain (x + (b - x)/2) hy_in
      have hy4 : 2 * (x + (b - x)/2) - (x + (b - x)/2) ^ 2 < 2 * x - x ^ 2 := by
        nlinarith [sq_nonneg ((x + (b - x)/2) - 1), sq_nonneg ((x - 1)), sq_pos_of_pos (show (0 : ℝ) < (b - x) by nlinarith)]
      have hy5 : f (x + (b - x)/2) < f x := by
        rw [hf]
        have h8 : 2 * (x + (b - x)/2) - (x + (b - x)/2) ^ 2 > 0 := hy3
        have h9 : 2 * x - x ^ 2 > 0 := hdomain x ⟨hx1, hx2⟩
        have h10 : logb 2 (2 * (x + (b - x)/2) - (x + (b - x)/2) ^ 2) < logb 2 (2 * x - x ^ 2) := by
          apply Real.logb_lt_logb
          all_goals nlinarith
        simpa using h10
      have hy6 : f x ≤ f (x + (b - x)/2) := hmono (show x ∈ Set.Ioo a b by
        exact ⟨hx1, hx2⟩
      ) (show (x + (b - x)/2) ∈ Set.Ioo a b by
        exact hy_in
      ) (show x ≤ x + (b - x)/2 by
        nlinarith
      )
      linarith
    constructor
    · linarith
    · linarith
  · -- Backward direction: if $(a,b) \subseteq (0,1)$, then $f$ is monotone on $(a,b)$
    intro hsubset
    intro x hx y hy hxy
    have hx1 : a < x := hx.1
    have hx2 : x < b := hx.2
    have hy1 : a < y := hy.1
    have hy2 : y < b := hy.2
    have hx5 : x ∈ Set.Ioo 0 1 := hsubset ⟨hx1, hx2⟩
    have hy5 : y ∈ Set.Ioo 0 1 := hsubset ⟨hy1, hy2⟩
    have hx6 : 0 < x := hx5.1
    have hx7 : x < 1 := hx5.2
    have hy6 : 0 < y := hy5.1
    have hy7 : y < 1 := hy5.2
    have h2 : 2 * x - x ^ 2 > 0 := by nlinarith
    have h3 : 2 * y - y ^ 2 > 0 := by nlinarith
    have h4 : 2 * x - x ^ 2 ≤ 2 * y - y ^ 2 := by nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x - y)]
    have h5 : logb 2 (2 * x - x ^ 2) ≤ logb 2 (2 * y - y ^ 2) := by
      apply Real.logb_le_logb_of_le
      all_goals nlinarith
    rw [hf]
    simp
    all_goals try linarith