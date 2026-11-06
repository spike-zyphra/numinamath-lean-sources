import Mathlib

open Real

theorem inequalities_259235 {n : ℕ} (hn : 2 ≤ n) (x : ℕ → ℝ)
    (hx : ∀ i ∈ Finset.Icc 1 n, 0 ≤ x i ∧ x i ≤ 1) :
    ∃ i ∈ Finset.Icc 1 (n - 1), x 1 * (1 - x (i + 1)) ≥ (1 / 4) * x 1 * (1 - x n) := by 
  use n - 1
  constructor 
  · -- Show that n - 1 is in the interval [1, n - 1]. 
    rw [Finset.mem_Icc]
    constructor 
    · -- Show 1 ≤ n - 1.
      omega 
    · -- Show n - 1 ≤ n - 1.
      omega 
  · -- Prove the inequality x 1 * (1 - x ((n - 1) + 1)) ≥ (1 / 4) * x 1 * (1 - x n)
    have eq1 : ((n - 1) + 1 : ℕ) = n := by 
      omega 
    rw [eq1] 
    have hx11 := hx 1 (by 
      have h5 : (1 : ℕ) ∈ Finset.Icc 1 n := by
        simp at *
        all_goals omega 
      exact h5 
    )
    have hxn1 := hx n (by 
      have h5 : (n : ℕ) ∈ Finset.Icc 1 n := by
        simp at *
        all_goals omega 
      exact h5 
    )
    rcases hx11 with ⟨hx11l, hx11r⟩ 
    rcases hxn1 with ⟨hxn1l, hxn1r⟩ 
    nlinarith
  all_goals nlinarith