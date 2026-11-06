import Mathlib

theorem number_theory_288155 (n : ℕ) :
    60 ∣ n^6 - n^2 := by
  have h1 : (n ^ 6) % 4 = (n ^ 2) % 4 := by
    have h2 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
      omega
    rcases h2 with (h2 | h2 | h2 | h2) <;> simp [h2, pow_succ, Nat.mul_mod]
  
  have h2 : (n ^ 6) % 3 = (n ^ 2) % 3 := by
    have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      omega
    rcases h3 with (h3 | h3 | h3) <;> simp [h3, pow_succ, Nat.mul_mod]

  have h3 : (n ^ 6) % 5 = (n ^ 2) % 5 := by
    have h4 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
      omega
    rcases h4 with (h4 | h4 | h4 | h4 | h4) <;> simp [h4, pow_succ, Nat.mul_mod]

  -- From $n^6 \equiv n^2 \pmod{4}$, we have $n^6 - n^2 \equiv 0 \pmod{4}$
  -- From $n^6 \equiv n^2 \pmod{3}$, we have $n^6 - n^2 \equiv 0 \pmod{3}$
  -- From $n^6 \equiv n^2 \pmod{5}$, we have $n^6 - n^2 \equiv 0 \pmod{5}$
  -- Since $n^6 - n^2$ is divisible by 4, 3, and 5, it's divisible by 60.
  omega