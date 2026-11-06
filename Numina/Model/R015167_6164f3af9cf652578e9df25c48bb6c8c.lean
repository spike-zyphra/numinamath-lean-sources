import Mathlib

open Real

theorem algebra_3572 : ∑ k ∈ (Finset.Icc (1:ℕ) 2005), √(1 + 1/(k^2:ℝ) + 1/((k+1)^2:ℝ)) = 2005 + 2005/2006 := by
  have h1 : ∀ k : ℕ, k ≥ 1 → √(1 + (1 / (k ^ 2 : ℝ)) + (1 / ((k + 1) ^ 2 : ℝ))) = 1 + 1 / ((k : ℝ) * ((k + 1 : ℝ))) := by
    intro k hk
    have h3 : (1 + (1 / (k ^ 2 : ℝ)) + (1 / ((k + 1) ^ 2 : ℝ))) = (1 + 1 / ((k : ℝ) * ((k + 1 : ℝ)))) ^ 2 := by
      field_simp
      ring_nf
    have h4 : √(1 + (1 / (k ^ 2 : ℝ)) + (1 / ((k + 1) ^ 2 : ℝ))) = √((1 + 1 / ((k : ℝ) * ((k + 1 : ℝ)))) ^ 2) := by
      rw [h3]
    have h5 : 1 + 1 / ((k : ℝ) * ((k + 1 : ℝ))) ≥ 0 := by
      have hk1 : (k : ℝ) ≥ 1 := by exact_mod_cast show (k : ℝ) ≥ (1 : ℝ) by exact_mod_cast hk
      have hk2 : (k + 1 : ℝ) ≥ 2 := by nlinarith
      positivity
    have h7 : √((1 + 1 / ((k : ℝ) * ((k + 1 : ℝ)))) ^ 2) = 1 + 1 / ((k : ℝ) * ((k + 1 : ℝ))) := by
      rw [Real.sqrt_sq (show (0 : ℝ) ≤ 1 + 1 / ((k : ℝ) * ((k + 1 : ℝ))) by linarith)]
    rw [h4, h7]

  have h2 : ∑ k in Finset.Icc (1 : ℕ) 2005, √(1 + 1/(k^2:ℝ) + 1/((k+1)^2:ℝ)) = ∑ k in Finset.Icc (1 : ℕ) 2005, (1 + 1 / ((k : ℝ) * ((k + 1 : ℝ)))) := by
    apply Finset.sum_congr
    . rfl
    intro k hk
    have hk1 : k ≥ 1 := by
      have h2 : k ∈ Finset.Icc (1 : ℕ) 2005 := by
        exact hk
      simp at h2 ⊢
      omega
    exact h1 k hk1

  rw [h2]

  have h3 : ∀ n : ℕ, ∑ k in Finset.Icc (1 : ℕ) n, (1 + 1 / ((k : ℝ) * ((k + 1 : ℝ)))) = (↑n : ℝ) + (↑n / ((↑n + 1 : ℝ))) := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [ih]
      field_simp at *
      ring_nf

  have h4 : ∑ k in Finset.Icc (1 : ℕ) 2005, (1 + 1 / ((k : ℝ) * ((k + 1 : ℝ)))) = (2005 : ℝ) + (2005 / 2006 : ℝ) := by
    specialize h3 2005
    norm_num at h3 ⊢
    linarith

  linarith