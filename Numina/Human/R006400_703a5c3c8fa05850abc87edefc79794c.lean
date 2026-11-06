import Mathlib.Tactic

/--
Let $j$ be a non-negative integer. Define the number $N_j = 888 + 3660j$.
Show that $2^{N_j} - N_j$ is divisible by $61$.-/
theorem divisibility_by_61 (j : ℕ) : 61 ∣ (2^(888 + 3660 * j) - (888 + 3660 * j)) := by
  -- First, we prove that for all j, 2^(888 + 3660*j) ≡ (888 + 3660*j) mod 61
  have h2 : ∀ j : ℕ, 2 ^ (888 + 3660 * j) % 61 = (888 + 3660 * j) % 61 := by
    intro j
    -- We proceed by induction on j
    induction j with
    | zero =>
      -- Base case (j = 0): Verify 2^888 ≡ 888 mod 61 by direct computation
      norm_num  -- Simplifies numerical expressions
    | succ j ih =>
      -- Inductive step: Assume the claim holds for j, prove it for j+1
      have h3 : 2 ^ (888 + 3660 * (j + 1)) % 61 = (888 + 3660 * (j + 1)) % 61 := by
        -- Expand the exponent: 888 + 3660*(j+1) = (888 + 3660*j) + 3660
        have h4 : 2 ^ (888 + 3660 * (j + 1)) = 2 ^ (888 + 3660 * j) * 2 ^ 3660 := by
          ring_nf  
        rw [h4]  
        -- We know 2^3660 ≡ 1 mod 61 (from Fermat's Little Theorem, since 61 is prime)
        have h5 : 2 ^ 3660 % 61 = 1 := by
          norm_num  -- Computes this explicitly (since 3660 = 60*61 and 2^60 ≡ 1 mod 61)
        -- Use the property (a * b) mod m = ((a mod m) * (b mod m)) mod m
        have h6 : (2 ^ (888 + 3660 * j) * 2 ^ 3660) % 61 = (2 ^ (888 + 3660 * j) % 61 * (2 ^ 3660 % 61)) % 61 := by
          rw [Nat.mul_mod]  -- Applies the modular multiplication rule
        rw [h6]  
        rw [h5]  
        simp [ih]  
        omega  
      exact h3  
  -- Now apply the general result h2 to our specific j
  have h1 : 2 ^ (888 + 3660 * j) % 61 = (888 + 3660 * j) % 61 := h2 j
  -- Finally, convert the congruence into divisibility: if a ≡ b mod m, then m ∣ (a - b)
  exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h1)
