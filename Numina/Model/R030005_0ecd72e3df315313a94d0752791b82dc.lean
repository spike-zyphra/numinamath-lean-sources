import Mathlib

theorem algebra_296803 {a : ℕ → ℤ} (ha1 : a 1 = 3)
    (han : ∀ n, a (n + 1) = (a n)^2 - (n + 1) * a n + 1) :
    ∀ n, ∑ i in Finset.range n, a (i + 1) = n * (n + 5) / 2 := by 
  intro n
  have h4 : ∀ (k : ℕ), a (k + 1) = k + 3 := by
    intro k 
    induction k with
    | zero =>
      have eq_a1 : a 1 = 3 := ha1
      simp at *
      all_goals linarith 
    | succ m ih =>
      have eq3 := han (m + 1)
      simp [ih] at eq3 ⊢
      <;> nlinarith 
  induction n with
  | zero => 
    simp 
  | succ n ih => 
    rw [Finset.sum_range_succ, ih]
    have eq_a_n : a (n + 1) = n + 3 := h4 n
    simp [eq_a_n]
    all_goals
      ring_nf 
      <;> omega