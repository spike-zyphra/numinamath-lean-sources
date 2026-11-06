import Mathlib

theorem algebra_189754 (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * (i + 2) / 2 = n * (n + 1) * (n + 2) / 6 := by
  induction n with
  | zero =>
    simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have eq1 : k * (k + 1) * (k + 2) / 6 + (k + 1) * (k + 2) / 2 =
        (k + 1) * (k + 2) * (k + 3) / 6 := by
      have h1 : k * (k + 1) * (k + 2) % 6 = 0 := by
        have h1 : k % 6 = 0 ∨ k % 6 = 1 ∨ k % 6 = 2 ∨ k % 6 = 3 ∨ k % 6 = 4 ∨ k % 6 = 5 := by
          omega
        rcases h1 with (h | h | h | h | h | h) <;> simp [h, Nat.add_mod, Nat.mul_mod]
      have h2 : (k + 1) * (k + 2) % 2 = 0 := by
        have h1 : k % 2 = 0 ∨ k % 2 = 1 := by
          omega
        rcases h1 with (h | h) <;> simp [h, Nat.add_mod, Nat.mul_mod]
      have h3 : k * (k + 1) * (k + 2) % 6 = 0 := h1
      have h4 : ( (k + 1) * (k + 2) ) % 2 = 0 := h2
      have eq5 : k * (k + 1) * (k + 2) + 3 * ((k + 1) * (k + 2)) =
          (k + 1) * (k + 2) * (k + 3) := by
        ring
      have eq6 : k * (k + 1) * (k + 2) / 6 + (k + 1) * (k + 2) / 2 = (k * (k + 1) * (k + 2) + 3 * ((k + 1) * (k + 2)) ) / 6 := by
        have h7 : k * (k + 1) * (k + 2) % 6 = 0 := h1
        have h8 : (k + 1) * (k + 2) % 2 = 0 := h2
        omega
      rw [eq6]
      rw [eq5]
      all_goals omega
    exact eq1