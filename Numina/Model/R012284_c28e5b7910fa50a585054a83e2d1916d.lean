import Mathlib

open Finset

theorem number_theory_201291 {k : ℕ → ℕ}
    (hk : ∀ a, k a = {p : ℕ × ℕ | p.1 ∈ Icc 1 a ∧ p.2 ∈ Icc 1 a ∧ Nat.Coprime p.1 p.2}.ncard) :
    ∑ i ∈ Icc 1 100, k (100 / i) = (100 ^ 2) := by 
  have h1 : ∑ i ∈ Icc 1 100, k (100 / i) = 10000 := by 
    have h2 : ∀ (i : ℕ), i ∈ Icc 1 100 → k (100 / i) = 
        Finset.card (Finset.filter (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2) ((Icc 1 (100 / i)) ×ˢ (Icc 1 (100 / i)))) := by 
      intro i hi 
      have h3 : k (100 / i) = {p : ℕ × ℕ | p.1 ∈ Icc 1 (100 / i) ∧ p.2 ∈ Icc 1 (100 / i) ∧ Nat.Coprime p.1 p.2}.ncard := by 
        specialize hk (100 / i)
        simpa using hk 
      have h4 : {p : ℕ × ℕ | p.1 ∈ Icc 1 (100 / i) ∧ p.2 ∈ Icc 1 (100 / i) ∧ Nat.Coprime p.1 p.2} = 
          ↑(Finset.filter (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2) ((Icc 1 (100 / i) ) ×ˢ (Icc 1 (100 / i))
          )) := by 
        ext ⟨x, y⟩ 
        simp [Finset.mem_Icc, Finset.mem_filter]
        <;> aesop 
      rw [h4] at h3
      rw [Set.ncard_coe_Finset] at h3 
      exact h3 
    have h3 : ∑ i ∈ Icc 1 100, k (100 / i) = 
        ∑ i ∈ Icc 1 100, Finset.card (Finset.filter (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2) ((Icc 1 (100 / i)) ×ˢ (Icc 1 (100 / i)))) := by 
      apply sum_congr 
      · rfl 
      · intro i hi 
        exact h2 i hi 
    rw [h3] 
    native_decide 
  calc 
    ∑ i ∈ Icc 1 100, k (100 / i) = 10000 := h1 
    _ = 100 ^ 2 := by norm_num