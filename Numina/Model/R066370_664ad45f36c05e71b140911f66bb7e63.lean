import Mathlib

theorem number_theory_67326 (A B k : ℕ) (hA : A < 10) (hB : B < 10)
    (hAB : (10 * A + B) * (10 * B + A) = k) (hk : 101 ∣ k + 1) :
    k = 403 := by 
  interval_cases A <;> interval_cases B <;> omega