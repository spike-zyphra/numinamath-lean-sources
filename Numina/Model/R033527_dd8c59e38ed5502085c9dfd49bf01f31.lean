import Mathlib

theorem number_theory_15702 : IsGreatest {n : ℕ | ∀ m : ℕ+, n ∣ m.val * (m.val + 1) * (m.val + 2)} 6 := by 
  constructor
  · -- Show that 6 is in the set.
    show ∀ m : ℕ+, 6 ∣ m.val * (m.val + 1) * (m.val + 2)
    intro m
    -- We need to prove that 6 divides the product. 
    -- To show this, we can prove that the product is divisible by both 2 and 3, which implies it is divisible by 6.
    -- We compute the product modulo 6
    have h1 : m.val * (m.val + 1) * (m.val + 2) % 6 = 0 := by
      have h2 : m.val % 6 = 0 ∨ m.val % 6 = 1 ∨ m.val % 6 = 2 ∨ m.val % 6 = 3 ∨ m.val % 6 = 4 ∨ m.val % 6 = 5 := by
        omega
      rcases h2 with (h | h | h | h | h | h) <;> simp [h, Nat.mul_mod, Nat.add_mod] 
    -- Now, prove the divisibility from the modulo result
    have h2 : 6 ∣ m.val * (m.val + 1) * (m.val + 2) := by
      omega
    exact h2
  · -- Show that any n in the set is ≤ 6
    intro n hn
    -- Assume n is in the set: ∀ m: ℕ+, n ∣ m.val * (m.val + 1) * (m.val + 2)
    -- We need to show n ≤ 6
    -- Let's take a specific instance: m = 1
    have h2 := hn (1)
    -- This means n divides 1.val * (1.val + 1) * (1.val + 2) which simplifies to 1 * 2 * 3 = 6
    norm_num at h2 
    -- So, n divides 6
    -- Now, from the fact that n divides 6, we have n ≤ 6
    have h1 : n ≤ 6 := by 
      exact Nat.le_of_dvd (by norm_num) h2 
    -- From n ≤ 6, we have the desired result
    linarith 
  all_goals try tauto