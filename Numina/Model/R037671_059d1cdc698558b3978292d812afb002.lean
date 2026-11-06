import Mathlib

theorem number_theory_220344 {n : ℕ} (hn : n ∈ Finset.Icc 100 999) (h : 10101 % n = 13226 % n) :
    10101 % n = 101 := by
  rw [Finset.mem_Icc] at hn
  rcases hn with ⟨hn1, hn2⟩
  interval_cases n <;> norm_num at h ⊢ <;> omega