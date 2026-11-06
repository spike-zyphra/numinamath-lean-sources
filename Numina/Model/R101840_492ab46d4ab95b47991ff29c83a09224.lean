import Mathlib

theorem number_theory_287760 (n : ℕ) (h : n > 0) (N : ℕ) (hN : N = (n * (n + 1) * (n + 2)) - (n + (n + 1) + (n + 2))) :
    Odd N → ∃ k, N = k * (k + 2) * (k + 4) := by
  intro hN_odd
  refine' ⟨n - 1, by
    rw [hN]
    cases n with
    | zero =>
      linarith
    | succ n => 
      simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
      <;> ring_nf
      <;> omega
  ⟩
  all_goals
  try { tauto }
  all_goals
  try { linarith }
  all_goals
  try { tauto }
  <;> try { 
    cases n
    all_goals try tauto
    all_goals try linarith
    <;> tauto
    <;> nlinarith 
    <;> nlinarith
  }