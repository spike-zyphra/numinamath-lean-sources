import Mathlib

theorem number_theory_218034 (n : ℕ) (h₀ : n ∈ Finset.Icc 1 100) (h₁ : Odd n) (h₂ : Odd (n + 2)) (h₃ : (100 - 2) * 51 = ∑ i ∈ Finset.Icc 1 100 \ {n, n + 2}, i) :
    n * (n + 2) = 675 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨hn1, hn2⟩
  have h₄ : n = 25 := by
    have h₅ : ∑ i ∈ Finset.Icc 1 100 \ {n, n + 2}, i = 4998 := by 
      nlinarith
    have h₇ : n ≤ 100 := by linarith 
    interval_cases n <;> try { 
      norm_num [Finset.sum_insert, Finset.sum_singleton] at h₃ h₅ ⊢ 
      <;> try tauto 
      all_goals omega 
    }
  calc
    n * (n + 2) = 25 * (25 + 2) := by rw [h₄]
    _ = 25 * 27 := by rfl
    _ = 675 := by norm_num