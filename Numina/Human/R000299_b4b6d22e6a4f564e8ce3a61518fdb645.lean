import Mathlib

/-
The sum of two prime numbers is  $85$ . What is the product of these two prime numbers?
-/

theorem number_theory_8856
    (p q : ℕ)
    (h₀ : p ≠ q)
    (h₁ : p + q = 85)
    (h₂ : Nat.Prime p)
    (h₃ : Nat.Prime q) :
    p * q = 166 := by

  -- Since $85$ is an odd number, there must be one even number in the two primes, thus one of them equals $2$.
  have : Even p ∨ Even q := by
    by_contra! h
    obtain ⟨h1, h2⟩ := h
    simp at h1 h2
    have : Even (p + q) := Odd.add_odd h1 h2
    rw [h₁] at this
    contradiction

  have : p = 2 ∨ q = 2 := by
    rcases this with h | h
    . left; exact (Nat.Prime.even_iff h₂).mp h
    . right; exact (Nat.Prime.even_iff h₃).mp h

  -- Then we know the other prime number is $85 - 2 = 83$. So their product is $2 * 83 = 166$.
  rcases this with h | h
  . apply Nat.eq_sub_of_add_eq' at h₁
    rw [h, show 85 - 2 = 83 by norm_num] at h₁
    norm_num [h₁, h]
  . apply Nat.eq_sub_of_add_eq at h₁
    rw [h, show 85 - 2 = 83 by norm_num] at h₁
    norm_num [h₁, h]
