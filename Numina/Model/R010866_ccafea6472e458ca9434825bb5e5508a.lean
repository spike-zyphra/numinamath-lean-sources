import Mathlib

theorem algebra_19894 (R : Finset ℤ) (hR : R = { n : ℤ | (2 - (-1)) ^ 2 + (n - 1) ^ 2 = 5 ^ 2 }) :
    R.prod id = -15 := by 
  have h12 : { n : ℤ | (2 - (-1)) ^ 2 + (n - 1) ^ 2 = 5 ^ 2 } = {-3, 5} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- If $(2 - (-1))^2 + (n - 1)^2 = 5^2$, then $n \in \{-3, 5\}$.
      intro h
      have h1 : (2 - (-1) : ℤ) ^ 2 + (n - 1 : ℤ) ^ 2 = (5 : ℤ) ^ 2 := by 
        nlinarith 
      have h4 : (n - 1 : ℤ) ^ 2 = 16 := by
        nlinarith 
      have h5 : (n - 1 : ℤ) = 4 ∨ (n - 1 : ℤ) = -4 := by 
        have h8 : (n - 1 : ℤ) ^ 2 - 16 = 0 := by 
          linarith 
        have h9 : (n - 1 - 4 : ℤ) * (n - 1 + 4 : ℤ) = 0 := by 
          nlinarith 
        cases' (mul_eq_zero.1 h9) with h10 h11
        · 
          left 
          omega 
        · 
          right 
          omega 
      cases h5 with 
      | inl h9 => 
        omega 
      | inr h9 => 
        omega 
    · -- If $n \in \{-3, 5\}$, then $(2 - (-1))^2 + (n - 1)^2 = 5^2$.
      rintro (h | h)
      · -- Case n = -3
        rw [show n = -3 by omega] 
        norm_num 
      · -- Case n = 5
        rw [show n = 5 by omega] 
        norm_num 
  have h2 : R = {-3, 5} := by 
    have h4 : (↑R : Set ℤ) = { n : ℤ | (2 - (-1)) ^ 2 + (n - 1) ^ 2 = 5 ^ 2 } := by 
      exact_mod_cast hR 
    have h5 : (↑R : Set ℤ) = ({-3, 5} : Set ℤ) := by 
      rw [h4] 
      exact h12 
    have h20 : R = ({-3, 5} : Finset ℤ) := by 
      have h24 : (↑R : Set ℤ) = (↑({-3, 5} : Finset ℤ) : Set ℤ) := by 
        simpa using h5 
      exact_mod_cast h24 
    exact h20 
  rw [h2] 
  all_goals 
    native_decide