import Mathlib

open Int Finset

theorem number_theory_131132 (a : Fin 5 → ℤ) (h : 9 ∣ ∑ k : Fin 5, (a k)^3) :
    3 ∣ ∏ k : Fin 5, a k := by
  by_contra h1
  have h1' : ¬ (3 ∣ ∏ k : Fin 5, a k) := h1
  -- If the product is not divisible by 3, then none of the factors is divisible by 3.
  have h4 : ∀ k : Fin 5, ¬ (3 ∣ a k) := by 
    intro k 
    by_contra h5 
    have h6 : 3 ∣ a k := h5
    have h7 : 3 ∣ ∏ k : Fin 5, a k := by
      have h8 : ∏ k : Fin 5, a k = (a k) * (∏ k' in (Finset.univ : Finset (Fin 5)) \ {k}, a k') := by
        rw [Finset.prod_eq_mul_prod_diff_singleton]
        all_goals simp
      rw [h8]
      apply dvd_mul_of_dvd_left 
      exact h6 
    contradiction 
  -- Therefore, each a_k ≡ 1 or 2 (mod 3).
  have h5 : ∀ k : Fin 5, a k % 3 = 1 ∨ a k % 3 = 2 := by
    intro k 
    have h4k : ¬ (3 ∣ a k) := h4 k 
    omega 
  -- Therefore, each (a_k)^3 ≡ 1 or 8 (mod 9).
  have h6 : ∀ k : Fin 5, (a k)^3 % 9 = 1 ∨ (a k)^3 % 9 = 8 := by
    intro k
    have h5k : a k % 3 = 1 ∨ a k % 3 = 2 := h5 k 
    have h8 : a k % 9 = 1 ∨ a k % 9 = 2 ∨ a k % 9 = 4 ∨ a k % 9 = 5 ∨ a k % 9 = 7 ∨ a k % 9 = 8 := by 
      omega 
    rcases h8 with (h8 | h8 | h8 | h8 | h8 | h8)
    all_goals 
      simp [pow_three, Int.add_emod, Int.mul_emod, h8] 
  -- Therefore the sum of the cubes cannot be divisible by 9.
  -- The sum is ∑ k : Fin 5, (a k)^3 % 9.
  -- Now we have contradiction.
  have h7 : (∑ k : Fin 5, (a k)^3) % 9 = 0 := by 
    omega 
  -- Now we prove that the sum is not = 0.
  have h8 : (∑ k : Fin 5, (a k)^3) % 9 ≠ 0 := by
    -- The sum of five terms, each of which is 1 or 8 (mod 9), cannot be 0 (mod 9).
    -- Let's compute all possible sums.
    have h9 : ∀ k : Fin 5, (a k)^3 % 9 = 1 ∨ (a k)^3 % 9 = 8 := by 
      intro k 
      apply h6 k
    -- Let's write all possible expressions.
    have h110 : (∑ k : Fin 5, (a k)^3) = (a 0)^3 + (a 1)^3 + (a 2)^3 + (a 3)^3 + (a 4)^3 := by 
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    rw [h110] 
    have h90 : (a 0)^3 % 9 = 1 ∨ (a 0)^3 % 9 = 8 := h9 0 
    have h91 : (a 1)^3 % 9 = 1 ∨ (a 1)^3 % 9 = 8 := h9 1 
    have h92 : (a 2)^3 % 9 = 1 ∨ (a 2)^3 % 9 = 8 := h9 2 
    have h93 : (a 3)^3 % 9 = 1 ∨ (a 3)^3 % 9 = 8 := h9 3 
    have h94 : (a 4)^3 % 9 = 1 ∨ (a 4)^3 % 9 = 8 := h9 4 
    omega 
  -- Now we have ((∑ k : Fin 5, (a k)^3) % 9 = 0) and ( (∑ k : Fin 5, (a k)^3) % 9 ≠ 0). Contradiction.
  contradiction