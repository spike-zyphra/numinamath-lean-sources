import Mathlib

def a (n : ℕ) := 4^(2*n + 1) + 3^(n + 2)

theorem number_theory_256456 :
    IsLeast {p | p.Prime ∧ ∀ n, p ∣ a n} 5 ∧
    IsLeast {p | p.Prime ∧ ∀ n, p ∣ a n ∧ ¬(p = 5)} 7 → ¬(5 * 7 = p * q) := by
  intro h
  rcases h with ⟨h1, h2⟩
  have h11 : 5 ∈ {p | p.Prime ∧ ∀ n, p ∣ a n} := by
    exact h1.left
  have h50 : (5 : ℕ) ∣ a 0 := by
    have h5_mem : 5 ∈ {p | p.Prime ∧ ∀ n, p ∣ a n} := h11
    have h10 : ∀ n, (5 : ℕ) ∣ a n := by 
      simp at h5_mem ⊢
      tauto
    specialize h10 0 
    simpa using h10
  norm_num [a] at h50 
  all_goals omega