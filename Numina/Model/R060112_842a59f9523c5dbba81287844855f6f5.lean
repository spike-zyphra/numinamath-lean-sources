import Mathlib

theorem number_theory_236923 (a b : ℕ) (ha : a ∈ Finset.Icc 10 99) (hb : b ∈ Finset.Icc 10 99)
    (h : a * b = 7007) (h' : 7 ∣ a) (h'' : 7 ∣ b) : a + b = 168 := by
  rw [Finset.mem_Icc] at ha hb
  rcases ha with ⟨ha10, ha99⟩
  rcases hb with ⟨hb10, hb99⟩
  interval_cases a <;> omega