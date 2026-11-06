import Mathlib

/-
64. (9th grade) The number 7 is raised to the seventh power, the resulting number is again raised to the seventh power, and so on. This process is repeated 1000 times. What is the last digit of this number?
-/

theorem number_theory_191949 (a: ℕ→ℕ) (ha0: a 0 = 7) (h: ∀n, a (n+1) = (a n)^7): (a 1000) % 10 = 7 := by
  -- We prove that this operation has period 2. Then the claim follows directly.
  have lem : ∀n:ℕ, a (2*n) % 10 = 7 ∧ a (2*n+1) % 10 = 3 := by 
    intro n
    induction' n with n hn

    simp [h,ha0]

    have h1 : a (2 * (n + 1)) % 10 = 7 := by
      have : 2*(n+1) = 2*n+1+1 := by omega
      rw [this]
      have : a (2 * n + 1 + 1) = a (2*n+1)^7 := by apply h
      rw [this]
      rw [Nat.pow_mod]
      rw [hn.right]
    have h2 :  a (2*(n+1)+1) % 10 = 3 := by
      have : a (2*(n+1)+1) = a (2*(n+1))^7 := by apply h
      rw [this]
      rw [Nat.pow_mod]
      rw [h1]
    tauto
  
  have : (a 1000) % 10 = 7 := by
    have : a (2*500) % 10 = 7 := by
      specialize lem 500
      exact lem.left
    norm_num at this
    exact this
  exact this