import Mathlib

theorem number_theory_120030 (a b c : ℕ) (ha : a ∈ Finset.Icc 1 9) (hb : b ∈ Finset.Icc 0 9)
    (hc : c ∈ Finset.Icc 0 9) (h : 100 * a + 10 * b + c = (a + b + c) ^ 3) :
    512 = 100 * a + 10 * b + c := by
  rw [Finset.mem_Icc] at ha hb hc
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  rcases hc with ⟨hc1, hc2⟩
  interval_cases a <;> interval_cases b <;> interval_cases c <;> omega