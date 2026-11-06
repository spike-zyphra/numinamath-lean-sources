import Mathlib

theorem algebra_10473 (f : ℝ → ℝ) (a c : ℝ) (hf : ∀ x, f x = a * x ^ 2 - c)
    (h1 : -4 ≤ f 1 ∧ f 1 ≤ -1) (h2 : -1 ≤ f 2 ∧ f 2 ≤ 5) :
    -1 ≤ f 3 ∧ f 3 ≤ 20 := by
  have eq1 : f 1 = a - c := by
    rw [hf 1]
    ring
  have eq2 : f 2 = 4 * a - c := by
    rw [hf 2]
    ring
  have eq3 : f 3 = 9 * a - c := by
    rw [hf 3]
    ring
  have h11 : -4 ≤ a - c := by 
    linarith [h1.1, eq1]
  have h12 : a - c ≤ -1 := by 
    linarith [h1.2, eq1]
  have h21 : -1 ≤ 4 * a - c := by 
    linarith [h2.1, eq2]
  have h22 : 4 * a - c ≤ 5 := by 
    linarith [h2.2, eq2]
  constructor
  · -- Proof that -1 ≤ f 3
    linarith [eq3, h11, h12, h21, h22]
  · -- Proof that f 3 ≤ 20
    linarith [eq3, h11, h12, h21, h22]