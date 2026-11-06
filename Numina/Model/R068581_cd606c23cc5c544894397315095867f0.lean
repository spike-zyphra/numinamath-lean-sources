import Mathlib

theorem number_theory_155778 (F : ℕ → ℕ) (hF : ∀ n, F (n + 2) = F (n + 1) + F n)
    (hF0 : F 0 = 0) (hF1 : F 1 = 1) (n k : ℕ) :
    ∑ i in Finset.range (n + 1), (F i)^2 = F n * F (n + 1) := by
  induction n with
  | zero =>
    simp [hF0]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp [hF, hF0, hF1]
    <;> ring_nf <;> omega