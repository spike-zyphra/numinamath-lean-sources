import Mathlib

open Real
open scoped BigOperators

theorem number_theory_120890 {f : ℕ → ℕ → ℕ}
  (hf : ∀ n k, f n k = {x | 0 < x ∧ x ≤ n / k ∧ Nat.Coprime x n}.encard) :
  f 100 3 = 14 := by
    have h1 : f 100 3 = {x | 0 < x ∧ x ≤ 100 / 3 ∧ Nat.Coprime x 100}.encard := hf 100 3
    have h2 : (f 100 3 : ℕ∞) = {x | 0 < x ∧ x ≤ 100 / 3 ∧ Nat.Coprime x 100}.encard := by 
      exact_mod_cast h1
    have h3 : 100 / 3 = 33 := by norm_num
    have h4 : {x | 0 < x ∧ x ≤ 100 / 3 ∧ Nat.Coprime x 100} = 
          Finset.filter (fun (x : ℕ) => 0 < x ∧ x ≤ 33 ∧ Nat.Coprime x 100) (Finset.Icc 0 33) := by
      ext x
      simp [h3]
      <;> omega
    rw [h4] at h2
    rw [Set.encard_coe_eq_coe_finsetCard] at h2
    have h5 : (f 100 3 : ℕ∞) = 14 := by 
      simp [Finset.filter] at h2 ⊢
      <;> try { native_decide }
      all_goals
        try { tauto }
      all_goals
        try { tauto }
      all_goals 
        try { native_decide }
      all_goals
        linarith
    have h5_nat : f 100 3 = 14 := by 
      have h6 : (f 100 3 : ℕ∞) = 14 := h5 
      exact_mod_cast h6
    exact h5_nat