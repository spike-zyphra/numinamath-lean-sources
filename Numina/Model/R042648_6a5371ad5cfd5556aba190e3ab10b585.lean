import Mathlib

theorem number_theory_22966 :
    IsLeast {n : ℕ | 0 < n ∧ (12500000 * n) % 999999999 = 111} 8880 := by
  constructor 
  · constructor 
    · norm_num
    · norm_num
  · intro n hn
    rcases hn with ⟨hn_pos, hn_mod⟩
    by_contra h
    push_neg at h
    have h1 : n > 0 := hn_pos
    have h2 : n < 8880 := by linarith
    -- Assume that n is a solution less than 8880, which would be a contradiction
    -- We have the congruence 12500000 * n ≡ 111 (mod 999999999)
    -- Let's compute the gcd of 12500000 and 999999999
    have h3 : (12500000 * n) % 999999999 = 111 := hn_mod 
    -- Since gcd of 12500000 and 999999999 is 1, the solution is unique
    have h41 : Nat.gcd 12500000 999999999 = 1 := by
      norm_num [Nat.gcd]
    have h42 : (12500000 : ℕ) * 80 % 999999999 = 1 := by
      norm_num
    -- Using the inverse of 12500000 (which is 80) to solve for n 
    -- The solutions must be congruent to 8880 modulo 999999999
    have h43 : n % 999999999 = 8880 := by 
      have h44 : (12500000 * n) % 999999999 = 111 := hn_mod
      have h45 : (12500000 * n : ℕ) % 999999999 = 111 := by 
        exact_mod_cast h44
      have h51 : (12500000 * n * 80 : ℕ) % 999999999 = (111 * 80 : ℕ) % 999999999 := by
        have h52 : (12500000 * n : ℕ) % 999999999 = 111 := by 
          exact_mod_cast h44
        have h53 : (12500000 * n * 80 : ℕ) % 999999999 = ( (12500000 * n : ℕ) % 999999999 * 80 ) % 999999999 := by
          simp [Nat.mul_mod]
        rw [h53]
        rw [h52]
      have h50 : (n : ℕ) % 999999999 = 8880 := by
        norm_num at h51 ⊢
        omega
      exact_mod_cast h50
    have h44 : n ≥ 8880 := by 
      omega
    linarith