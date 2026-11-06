import Mathlib

def d (n : ℕ) := n % 10

def k (n : ℕ) := n / 10

theorem number_theory_4864 :
    IsLeast {m | 0 < m ∧ ∀ n, 29 ∣ n → 29 ∣ m * k n + 6 * d n} 2 := by
  constructor
  · -- Show that 2 is in the set
    constructor
    · -- Show 0 < 2
      norm_num
    · -- Show ∀ n, 29 ∣ n → 29 ∣ 2 * k n + 6 * d n
      intro n hn
      have h1 : n % 29 = 0 := by
        omega
      have h2 : k n = n / 10 := by rfl
      have h3 : d n = n % 10 := by rfl
      have h5 : 29 ∣ 2 * k n + 6 * d n := by
        rw [show k n = n / 10 by rfl, show d n = n % 10 by rfl]
        omega
      exact h5
  · -- Show that 2 is the least
    intro m hm
    rcases hm with ⟨hm_pos, hm_prop⟩
    by_contra h
    push_neg at h
    have hm1 : m = 1 := by
      omega
    have h29 := hm_prop 29 (by norm_num)
    rw [hm1] at h29
    norm_num [k, d] at h29