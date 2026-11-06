import Mathlib

theorem number_theory_41257 (n : ℕ) :
    (n = 1981 → 1981 ∣ 145^n + 3114 * 138^n) ∧ (n = 1980 → ¬1981 ∣ 145^n + 3114 * 138^n) := by 
  constructor
  · -- Assume n = 1981 prove 1981 ∣ 145^n + 3114 * 138^n
    intro hn
    rw [hn]
    norm_num
  · -- Assume n = 1980 prove ¬1981 ∣ 145^n + 3114 * 138^n
    intro hn
    rw [hn]
    norm_num