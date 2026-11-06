import Mathlib

theorem number_theory_183938 (n : ℕ) (h : n ∈ Finset.Icc 100 999) :
    651 ∣ (594000 + n) ↔ n = 363 := by

  rw [Finset.mem_Icc] at h
  rcases h with ⟨h100, h999⟩
  constructor
  · -- Proof of first direction: If 651 divides 594000 + n, then n = 363
    intro hdiv
    omega
  · -- Proof of second direction: If n = 363, then 651 divides 594000 + n
    rintro hn
    rw [hn]
    norm_num