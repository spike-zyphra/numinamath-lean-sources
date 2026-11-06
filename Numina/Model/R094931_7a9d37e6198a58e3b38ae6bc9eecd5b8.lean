import Mathlib

theorem number_theory_241014 (a b c : ℕ) (ha : a ∈ Finset.Icc 10 99) (hb : b ∈ Finset.Icc 10 99)
    (hc : c ∈ Finset.Icc 1000 9999) (h1 : ∃ k, a = k * 11) (h2 : ∃ m, b = m * 11) (h3 : ∃ n, c = n * 1111)
    (h4 : a^2 + b = c) :
    (a = 33 ∧ b = 22 ∧ c = 1111) ∨ (a = 66 ∧ b = 88 ∧ c = 4444) ∨ (a = 88 ∧ b = 33 ∧ c = 7777) := by 
  rcases h1 with ⟨k, rfl⟩
  rcases h2 with ⟨m, rfl⟩
  rcases h3 with ⟨n, rfl⟩
  simp only [Finset.mem_Icc] at ha hb hc
  rcases ha with ⟨hk1, hk2⟩
  rcases hb with ⟨hm1, hm2⟩
  rcases hc with ⟨hn1, hn2⟩
  have k1 : k ≥ 1 := by nlinarith
  have k2 : k ≤ 9 := by nlinarith
  have m1 : m ≥ 1 := by nlinarith
  have m2 : m ≤ 9 := by nlinarith
  have n1 : n ≥ 1 := by nlinarith
  have n2 : n ≤ 9 := by nlinarith
  interval_cases k <;> interval_cases m <;> omega