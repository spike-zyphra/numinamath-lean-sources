import Mathlib

theorem number_theory_885 (n : ℕ) (h₀ : n ∈ Finset.Icc 0 9) : 6 ∣ 52280 + n ↔ n = 4 := by 
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₀₃, h₀₉⟩
  constructor
  · -- Forward: if $6 \mid 52280 + n$, then $n = 4$
    intro h
    omega
  · -- Backward: if $n = 4$, then $6 \mid 52280 + n$
    intro h
    subst n
    all_goals norm_num