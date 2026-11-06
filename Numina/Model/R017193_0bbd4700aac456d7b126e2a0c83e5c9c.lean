import Mathlib

theorem algebra_300165 {a b c d : ℝ} (hc : c ≠ 0) (h : a * d - b * c ≠ 0)
    (a_seq : ℕ → ℝ) (f : ℝ → ℝ) (hf : f = fun x => (a * x + b) / (c * x + d))
    (ha : a_seq 1 ≠ f (a_seq 1)) :
    (∃ x1 x2, x1 ≠ x2 ∧ f x1 = x1 ∧ f x2 = x2 →
      (a_seq (n + 1) - x1) / (a_seq (n + 1) - x2) =
        (a - c * x1) / (a - c * x2) * (a_seq n - x1) / (a_seq n - x2)) ∧
    (∃ x0, f x0 = x0 ∧ a ≠ -d →
      1 / (a_seq (n + 1) - x0) = 2 * c / (a + d) + 1 / (a_seq n - x0)) := by

  constructor
  · -- First impossible condition from substitution
    use 0, 0 
    intro h'
    exfalso 
    norm_num at h'
  · -- The second part 
    use a_seq 1 
    intro h'
    exfalso 
    have h1 : f (a_seq 1) = a_seq 1 := by
      tauto 
    have h2 : a_seq 1 = f (a_seq 1) := by 
      linarith [h1]
    tauto