import Mathlib

theorem algebra_273797 {a : ℕ → ℚ} (ha1 : a 1 = 1) (ha2 : a 2 = 3 / 7)
    (han : ∀ n ≥ 3, a n = a (n - 2) * a (n - 1) / (2 * a (n - 2) - a (n - 1))) :
    ∃ p q : ℕ, p > 0 ∧ q > 0 ∧ a 2019 = p / q ∧ p.gcd q = 1 := by
  have h1 : ∀ (n : ℕ), a (n + 1) = 3 / (4 * ((n + 1 : ℕ) : ℚ) - 1) := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      norm_num [ha1]
      <;> linarith 
    | succ n =>
      cases n with
      | zero => 
        norm_num [ha2]
        <;> linarith 
      | succ n =>
        have h3 := ih (n) (by linarith)
        have h4 := ih (n + 1) (by linarith)
        have eq1 : a (n + 1 + 1 + 1) = (a (n + 1) * a (n + 1 + 1)) / (2 * a (n + 1) - a (n + 1 + 1)) := by
          specialize han (n + 1 + 1 + 1) (by omega)
          simp [show n + 1 + 1 + 1 - 2 = n + 1 by omega, show n + 1 + 1 + 1 - 1 = n + 1 + 1 by omega] at han ⊢
          simpa using han
        rw [eq1, h3, h4]
        field_simp
        ring_nf
        <;> field_simp
        <;> ring_nf <;> field_simp <;> nlinarith
        all_goals
          ring_nf
          <;> field_simp
          <;> ring_nf
          <;> norm_num
          <;> nlinarith
  
  have h2019 : a 2019 = (3 : ℚ) / (8075 : ℚ) := by 
    specialize h1 2018
    norm_num at h1 ⊢
    linarith
  
  use 3, 8075
  constructor
  · norm_num 
  constructor
  · norm_num 
  constructor
  · rw [h2019]
    all_goals norm_num
  · -- (p, q) = 1
    norm_num [Nat.gcd]
  all_goals norm_num