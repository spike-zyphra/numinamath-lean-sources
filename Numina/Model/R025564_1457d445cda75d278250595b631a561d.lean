import Mathlib

theorem number_theory_5639 (n : ℕ) :
    ∃! h : ℕ → ℕ,
      h 0 = n ∧
      ∀ m, h (m + 1) = h m + n := by
  use fun m => (m + 1) * n
  constructor
  · -- Show that this function satisfies the conditions
    constructor
    · -- Show that $h_n(0) = n$
      simp [Nat.add_zero]
    · -- Show that for any $m$, $h_n(m+1) = h_n(m) + n$
      intro m
      simp [Nat.mul_add, Nat.add_mul, add_assoc, Nat.mul_assoc, Nat.add_left_comm]
      <;> ring_nf <;> omega
  · -- Show that the function is unique
    intro h ⟨h0, h1⟩
    funext m
    induction m with
    | zero =>
      simp [h0]
    | succ m ih =>
      have eq1 : h (m + 1) = h m + n := h1 m
      rw [eq1]
      simp [ih]
      <;> ring_nf <;> omega