import Mathlib

open Finset

theorem number_theory_46717 {W : ℕ → ℕ}
    (hW : W 1 = 0)
    (hW' : W 2 = 1)
    (hW'' : ∀ p, Odd p → Prime p → W p = 1 + W (p + 1))
    (hW''' : ∀ c, ¬Prime c → ∃ d, d = sSup {x | x ∣ c ∧ x < c} ∧ W c = 1 + W d) :
    IsGreatest {x | ∃ n, x = W n ∧ n < 100} 12 := by
  have h1 := hW''' 1 (by
    norm_num 
  )
  rcases h1 with ⟨d, h1_eq, h1_eq2⟩
  have h2 : sSup {x | x ∣ 1 ∧ x < 1} = 0 := by
    have h3 : {x | x ∣ 1 ∧ x < 1} = ∅ := by
      ext n 
      simp 
      <;> omega 
    rw [h3]
    simp
  rw [h2] at h1_eq 
  have h3 : d = 0 := by 
    omega
  have h4 : W 1 = 1 + W 0 := by
    rw [h3] at h1_eq2 
    omega 
  have h5 : W 1 = 0 := hW 
  omega