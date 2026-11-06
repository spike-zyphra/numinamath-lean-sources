import Mathlib

theorem number_theory_188694 (n : ℕ) (h : n ∈ Finset.Icc 100 999) (h1 : (n / 10) % 10 = n % 10 + n / 100) :
    11 ∣ n := by
  rw [Finset.mem_Icc] at h
  rcases h with ⟨h2, h3⟩
  interval_cases n <;> norm_num at h1 ⊢ <;> omega
  <;> try trivial
  <;> omega