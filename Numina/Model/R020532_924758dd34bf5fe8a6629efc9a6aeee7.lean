import Mathlib

theorem number_theory_86026 (a : ℕ) (ha : a ∈ Finset.range 10) :
    10 ∣ ∑ i ∈ Finset.range 10, (10 * i + a) ^ 2005 := by
  rw [Finset.mem_range] at ha
  have h1 : a < 10 := by 
    exact_mod_cast ha
  interval_cases a <;> native_decide