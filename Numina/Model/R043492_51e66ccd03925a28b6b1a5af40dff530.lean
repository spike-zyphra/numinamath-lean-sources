import Mathlib

def x (n : ℕ) : ℤ := match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => 3 * x (n + 1) - 2 * x n

def y (n : ℕ) := (x n)^2 + 2^(n + 2)

theorem number_theory_92046 {n : ℕ} (hn : n > 0) :
    ∃ m, Odd m ∧ y n = m^2 := by
  have h1 : ∀ (n : ℕ), x n = (2 ^ n : ℤ) - 1 := by 
    intro n
    induction' n using Nat.strongRecOn with n ih 
    cases n with 
    | zero =>
      simp [x]
    | succ n =>
      cases n with 
      | zero =>
        simp [x]
      | succ n =>
        have h2 := ih (n + 1) (by linarith)
        have h3 := ih (n) (by linarith)
        simp [x, h2, h3]
        ring_nf
  have h3 : y n = ((2 ^ n + 1 : ℤ)) ^ 2 := by 
    simp [y, h1]
    <;> ring_nf
  use (2 ^ n + 1 : ℤ)
  constructor 
  · -- Show that m is odd 
    have h5 : Odd (2 ^ n + 1 : ℤ) := by 
      have h6 : (2 ^ n : ℤ) % 2 = 0 := by 
        have h9 : n > 0 := hn
        have h8 : ∀ (k : ℕ), (2 : ℤ) ^ (k + 1) % 2 = 0 := by 
          intro k
          induction k with
          | zero => 
            norm_num 
          | succ k ih => 
            simp [pow_succ, pow_zero] at ih ⊢
            all_goals omega 
        specialize h8 (n - 1)
        have h7 : n - 1 + 1 = n := by omega 
        rw [h7] at h8 
        all_goals omega 
      have h50 : (2 ^ n + 1 : ℤ) % 2 = 1 := by 
        omega 
      exact ⟨(2 ^ n + 1) / 2, by omega⟩ 
    tauto
  · -- Show that y n = m^2
    linarith [h3]