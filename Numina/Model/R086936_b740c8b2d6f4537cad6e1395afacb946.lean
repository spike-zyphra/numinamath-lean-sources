import Mathlib

theorem number_theory_115583 (a b : ℕ) (ha : a > 0) (hb : b > 0)
    (h : ∑ i ∈ Finset.range a, (2 * i + 1) = ∑ i ∈ Finset.range b, (2 * i + 2)) :
    False := by
  have h1 : ∀ a : ℕ, ∑ i ∈ Finset.range a, (2 * i + 1) = a ^ 2 := by
    intro a
    induction a with
    | zero =>
      simp
    | succ a ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  have h2 : ∀ b : ℕ, ∑ i ∈ Finset.range b, (2 * i + 2) = b * (b + 1) := by
    intro b
    induction b with
    | zero =>
      simp
    | succ b ih =>
      rw [Finset.sum_range_succ, ih]
      simp [add_mul, mul_add]
      <;> ring
  have h_eq : a ^ 2 = b * (b + 1) := by 
    specialize h1 a
    specialize h2 b
    linarith 
  have h3 : a > b := by
    nlinarith [h_eq, sq_pos_of_pos (show 0 < b by linarith), mul_pos (show 0 < b by linarith) (show 0 < b + 1 by linarith)]
  have h4 : a < b + 1 := by
    nlinarith [h_eq, sq_pos_of_pos (show 0 < b by linarith), sq_pos_of_pos (show 0 < b + 1 by linarith), mul_pos (show 0 < b by linarith) (show 0 < b + 1 by linarith)]
  linarith