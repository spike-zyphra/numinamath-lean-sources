import Mathlib

theorem number_theory_211508 : ¬∃ x y z t : ℕ, 16^x + 21^y + 26^z = t^2 := by
  rintro ⟨x, y, z, t, h⟩

  have h1 : t ^ 2 % 5 = 0 ∨ t ^ 2 % 5 = 1 ∨ t ^ 2 % 5 = 4 := by 
    have h2 : t % 5 = 0 ∨ t % 5 = 1 ∨ t % 5 = 2 ∨ t % 5 = 3 ∨ t % 5 = 4 := by 
      omega
    rcases h2 with (h2 | h2 | h2 | h2 | h2) <;> 
      simp [h2, Nat.pow_mod]

  have h2 : (16 ^ x + 21 ^ y + 26 ^ z) % 5 = 3 := by
    have h16 : ∀ x : ℕ, (16 ^ x) % 5 = 1 := by
      intro x
      induction x with 
      | zero => 
        norm_num 
      | succ x ih => 
        simp [Nat.pow_succ, Nat.mul_mod] at ih ⊢
        all_goals
          omega
    have h21 : ∀ y : ℕ, (21 ^ y) % 5 = 1 := by
      intro y
      induction y with 
      | zero => 
        norm_num 
      | succ y ih => 
        simp [Nat.pow_succ, Nat.mul_mod] at ih ⊢
        all_goals
          omega
    have h26 : ∀ z : ℕ, (26 ^ z) % 5 = 1 := by
      intro z
      induction z with 
      | zero => 
        norm_num 
      | succ z ih => 
        simp [Nat.pow_succ, Nat.mul_mod] at ih ⊢
        all_goals
          omega
    have hx1 : (16 ^ x) % 5 = 1 := h16 x
    have hy1 : (21 ^ y) % 5 = 1 := h21 y
    have hz1 : (26 ^ z) % 5 = 1 := h26 z
    omega

  have h3 : t ^ 2 % 5 = 3 := by 
    omega

  omega