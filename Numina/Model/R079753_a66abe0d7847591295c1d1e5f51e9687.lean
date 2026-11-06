import Mathlib

theorem number_theory_242779 (n : ℕ) (h₀ : Odd n) (h₁ : ∀ i ∈ Finset.range 7, Odd (n + 2 * i)) (h₂ : ∀ i ∈ Finset.range 7, (n + 2 * i) < 77)
    (h₃ : (Nat.digits 10 (∑ i ∈ Finset.range 7, (n + 2 * i))).sum = 7) :
    n = 13 := by
  have h4 : n < 65 := by
    have h6 := h₂ 6 (by norm_num [Finset.mem_range])
    omega
  have h5 : ∑ i in Finset.range 7, (n + 2 * i) = 7 * n + 42 := by
    simp [Finset.sum_range_succ]
    <;> ring
  rw [h5] at h₃
  interval_cases n <;> norm_num at h₃ h₀ ⊢ <;> try { tauto }
  <;> contradiction