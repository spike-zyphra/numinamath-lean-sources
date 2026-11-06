import Mathlib

theorem number_theory_299238 (a b : ℕ) (ha : a ∈ Finset.Icc 10 99) (hb : b ∈ Finset.Icc 10 99)
    (h : a + b = 2008 - (10 * (b % 10) + (a % 10))) :
    a + b ≤ 68 := by 
  rw [Finset.mem_Icc] at ha hb
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  omega