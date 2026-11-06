import Mathlib

/-
Let $m$ be a non-negative integer. Let $N = 4m+3$. Determine the units digit of the sum $3^N + 4^N + 5^N$. Show that the units digit is 6.
-/


--We prove by induction the unit digit of 3^N.
lemma l3 (n: ℕ):
3^(4*n) % 10 = 1 ∧ 3^(4*n+1) % 10 = 3 ∧ 3^(4*n+2) % 10 = 9 ∧ 3^(4*n+3) % 10 = 7 := by 

  induction' n with n hn

  simp

  obtain ⟨h0,h1,h2,h3⟩ := hn

  have h4 : 3 ^ (4 * (n + 1)) % 10 = 1 := by 
    have : 4 * (n + 1) = 4*n+3+1 := by omega
    rw [this]
    rw [pow_succ]
    rw [Nat.mul_mod]
    rw [h3]
  have h5 : 3 ^ (4 * (n + 1) + 1) % 10 = 3 := by 
    rw [pow_succ]
    rw [Nat.mul_mod]
    rw [h4]
  have h6 : 3 ^ (4 * (n + 1) + 2) % 10 = 9 := by 
    rw [pow_succ]
    rw [Nat.mul_mod]
    rw [h5]
  have h7 : 3 ^ (4 * (n + 1) + 3) % 10 = 7 := by 
    rw [pow_succ]
    rw [Nat.mul_mod]
    rw [h6]

  tauto

--We prove by induction the unit digit of 4^N.
lemma l4 (n: ℕ):
4^(2*n+1) % 10 = 4 ∧ 4^(2*n+2) % 10 = 6 := by 
  induction' n with n hn

  simp

  obtain ⟨hn1,hn2⟩ := hn
  have t1 : 4 ^ (2 * (n + 1) + 1) % 10 = 4 := by
    rw [pow_succ]
    rw [Nat.mul_mod]
    have : 2 * (n + 1) = 2*n+2 := by ring
    rw [this]
    rw [hn2]

  have t2: 4 ^ (2 * (n + 1) + 2) % 10 = 6 := by
    have : 2 * (n + 1) + 2 = 2 * (n + 1) + 1 + 1 := by ring
    rw [this]
    rw [pow_succ]
    rw [Nat.mul_mod]
    rw [t1]

  tauto

--We prove by induction the unit digit of 5^N.
lemma l5 (n: ℕ):
5^(n+1) % 10 = 5 := by 
  induction' n with n hn

  simp

  rw [pow_succ]
  rw [Nat.mul_mod]
  rw [hn]

theorem number_theory_638700 (m N:ℕ) (hN: N = 4*m+3):
  (3^N + 4^N + 5^N)%10 = 6 := by
  

  --We simply apply the lemmas and then add them up.
  have e3 : 3^N % 10 = 7 := by
    have : 3^(4*m) % 10 = 1 ∧ 3^(4*m+1) % 10 = 3 ∧ 3^(4*m+2) % 10 = 9 ∧ 3^(4*m+3) % 10 = 7 := by apply l3
    rw [hN]
    exact this.right.right.right

  have e4 : 4^N % 10 = 4 := by 
    have exi : ∃n:ℕ, 2*n+1 = N := by
      use (2*m+1)
      omega
    obtain ⟨n, hn⟩ := exi
    have : 4^(2*n+1) % 10 = 4 ∧ 4^(2*n+2) % 10 = 6 := by apply l4
    rw [hn] at this
    exact this.left

  have e5 : 5^N % 10 = 5 := by 
    have exi : ∃n:ℕ, n+1 = N := by
      use N-1
      omega
    obtain ⟨n, hn⟩ := exi
    have : 5^(n+1) % 10 = 5 := by apply l5
    rw [hn] at this
    exact this

  rw [Nat.add_mod]
  nth_rw 2 [Nat.add_mod]
  simp [e3,e4,e5]