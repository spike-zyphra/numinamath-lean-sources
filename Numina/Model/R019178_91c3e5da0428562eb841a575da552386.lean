import Mathlib

theorem number_theory_152136 {P : ℕ} (hP : Nat.Prime P) (hP1 : P > 5) :
    ∃ p k, Nat.Prime p ∧ 7 ≤ p ∧ p ≤ 31 ∧ P = p + k * 30 := by 
  have h1 : P % 2 = 1 := by
    by_contra h
    have : ¬Nat.Prime P := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ P by omega) (by linarith) (by linarith)
    contradiction
  
  have h2 : P % 3 = 1 ∨ P % 3 = 2 := by
    by_contra h
    push_neg at h
    have : P % 3 = 0 := by
      omega 
    have : ¬Nat.Prime P := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ P by 
        omega 
      ) (by linarith) (by linarith)
    contradiction

  have h3 : P % 5 = 1 ∨ P % 5 = 2 ∨ P % 5 = 3 ∨ P % 5 = 4 := by
    by_contra h
    push_neg at h
    have : P % 5 = 0 := by
      omega 
    have : ¬Nat.Prime P := by
      apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ P by 
        omega 
      ) (by linarith) (by linarith)
    contradiction

  have h4 : P % 30 = 1 ∨ P % 30 = 7 ∨ P % 30 = 11 ∨ P % 30 = 13 ∨ P % 30 = 17 ∨ P % 30 = 19 ∨ P % 30 = 23 ∨ P % 30 = 29 := by
    omega
  
  rcases h4 with (h | h | h | h | h | h | h | h)
  · -- Case $P \equiv 1 \pmod{30}$
    use 31
    use (P - 31) / 30 
    constructor 
    · -- 31 is prime 
      norm_num 
    constructor 
    · norm_num 
    constructor 
    · norm_num
    · 
      omega
  
  · -- Case $P \equiv 7 \pmod{30}$
    use 7
    use (P - 7) / 30 
    constructor 
    · -- 7 is prime
      norm_num
    constructor 
    · norm_num 
    constructor
    · norm_num
    · 
      omega
  · -- Case $P \equiv 11 \pmod{30}$
    use 11
    use (P - 11) / 30 
    constructor
    · -- 11 is prime 
      norm_num 
    constructor
    · norm_num 
    constructor 
    · norm_num 
    · 
      omega 
  · -- Case $P \equiv 13 \pmod{30}$
    use 13 
    use (P - 13) / 30
    constructor
    · -- 13 is prime 
      norm_num 
    constructor
    · norm_num 
    constructor
    · norm_num 
    · 
      omega 
  · -- Case $P \equiv 17 \pmod{30}$
    use 17 
    use (P - 17) / 30
    constructor
    · -- 17 is prime 
      norm_num 
    constructor
    · norm_num 
    constructor
    · norm_num 
    · 
      omega 
  · -- Case $P \equiv 19 \pmod{30}$
    use 19 
    use (P - 19) / 30
    constructor
    · -- 19 is prime 
      norm_num 
    constructor
    · norm_num
    constructor
    · norm_num 
    · 
      omega
  · -- Case $P \equiv 23 \pmod{30}$
    use 23 
    use (P - 23) / 30 
    constructor 
    · -- 23 is prime
      norm_num 
    constructor
    · norm_num
    constructor
    · norm_num 
    · 
      omega
  · -- Case $P \equiv 29 \pmod{30}$
    use 29 
    use (P - 29) / 30 
    constructor 
    · -- 29 is prime
      norm_num 
    constructor
    · norm_num 
    constructor
    · norm_num 
    · 
      omega