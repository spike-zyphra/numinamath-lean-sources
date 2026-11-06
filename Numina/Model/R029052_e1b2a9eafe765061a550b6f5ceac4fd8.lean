import Mathlib

theorem number_theory_254941 :
  ∀ k : ℕ, k > 0 → 
  let row1 := k
  let row2 := 2*k - 2
  let row3 := 2*k - 1
  (row1 * row2)^2 + row3^2 = (row1 * row2 + 1)^2 := by
  intro k hk
  have h1 : 2 * k ≥ 2 := by
    omega
  have h4 : 2 * k - 2 ≥ 0 := by omega
  have h5 : (k * (2 * k - 2)) ^ 2 + (2 * k - 1) ^ 2 = (k * (2 * k - 2) + 1) ^ 2 := by
    cases k with
    | zero =>
      omega
    | succ k =>
      cases k with
      | zero =>
        simp
      | succ k =>
        simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul]
        <;> ring_nf <;> omega
  simpa using h5