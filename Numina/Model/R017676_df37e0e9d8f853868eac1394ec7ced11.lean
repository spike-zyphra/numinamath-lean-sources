import Mathlib

open Finset Real

theorem algebra_127920 {S : ℕ → ℝ}
    (hS : ∀ n, S n = ∑ i in Icc 1 n, i) :
    IsGreatest {x | ∃ n, x = S n / ((n + 32) * S (n + 1))} (1 / 50) := by
  have h11 : ∀ n : ℕ, S n = (n : ℝ) * (n + 1) / 2 := by
    intro n 
    rw [hS n]
    have h7 : ∀ (n : ℕ), (∑ i in Icc 1 n, (i : ℝ)) = (n : ℝ) * (n + 1) / 2 := by
      intro n
      induction n with 
      | zero => 
        simp 
      | succ n ih => 
        rw [sum_Icc_succ_top (by linarith)]
        rw [ih]
        field_simp 
        <;> ring 
    specialize h7 n 
    simpa using h7
  constructor
  · -- Show that 1/50 is in the set.
    use 8 
    rw [h11 8, h11 9]
    norm_num 
  · -- Show that no greater value is in the set.
    intro x hx 
    rcases hx with ⟨n, hn⟩ 
    rw [hn]
    have eq3 : S n = (n : ℝ) * (n + 1) / 2 := h11 n 
    have eq4 : S (n + 1) = ((n + 1 : ℝ) ) * (n + 2) / 2 := by
      have eq5 : S (n + 1) = ((n + 1 : ℝ) ) * ((n + 1 + 1) ) / 2 := by
        specialize h11 (n + 1)
        norm_num at h11 ⊢
        linarith
      ring_nf at eq5 ⊢ 
      linarith 
    rw [eq3, eq4]
    have h6 : ((n : ℝ) * (n + 1) / (2 : ℝ) ) / ( (n + (32 : ℝ)) * ( ((n + 1) : ℝ) * (n + 2) / (2 : ℝ) ) ) = (n / ((n + (32 : ℝ)) * (n + (2 : ℝ)) ) ) := by 
      field_simp 
      <;> ring_nf
    rw [h6]
    have h7 : (n / ((n + (32 : ℝ)) * (n + (2 : ℝ)) ) ) ≤ (1 / 50 : ℝ) := by
      have h8 : (50 * (n : ℝ)) ≤ ((n + (32 : ℝ)) * (n + (2 : ℝ)) ) := by 
        have h9 : (n : ℝ) ≥ (0 : ℝ) := by exact_mod_cast (show (n : ℕ) ≥ 0 by omega)
        nlinarith [sq_nonneg ((n : ℝ) - 8), sq_nonneg ((n : ℝ) + 2), sq_nonneg ((n : ℝ) + 32) ]
      have h9 : (n / ((n + (32 : ℝ)) * (n + (2 : ℝ)) ) ) ≤ (1 / 50 : ℝ) := by 
        apply (div_le_iff₀ (by positivity)).mpr 
        nlinarith 
      linarith 
    linarith