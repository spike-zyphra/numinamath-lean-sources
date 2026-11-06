import Mathlib
/- What is the last two digits of base-$3$ representation of $2005^{2003^{2004}+3}$?

$
\textbf{(A)}\ 21
\qquad\textbf{(B)}\ 01
\qquad\textbf{(C)}\ 11
\qquad\textbf{(D)}\ 02
\qquad\textbf{(E)}\ 22
$ -/
theorem number_theory_35692 : 2005 ^ (2003 ^ 2004 + 3) ≡ 2 * 3 ^ 1 + 1 * 3 ^ 0 [MOD 9]:= by
  -- Convert the right side of the congruence to decimal (7)
  rw [show 2 * 3 ^ 1 + 1 * 3 ^ 0 = 7 by simp]
  -- Define m as 2003^2004 + 3 for easier reference
  set m:= 2003 ^ 2004 + 3 with hm
  clear_value m
  -- Define n as 2004 for easier reference
  set n:= 2004 with hn
  clear_value n

  -- First, we establish that 2003 ≡ 2 (mod 3)
  have h1 : 2003 ≡ 2 [MOD 3]:= by rfl
  -- Therefore, 2003^n ≡ 2^n (mod 3)
  replace h1 : 2003 ^ n ≡ 2 ^ n [MOD 3]:= by exact Nat.ModEq.pow n h1
  -- Also, 3 ≡ 0 (mod 3)
  have h2 : 3 ≡ 0 [MOD 3]:= by rfl
  -- So 2003^n + 3 ≡ 2^n + 0 ≡ 2^n (mod 3)
  replace h1 : 2003 ^ n + 3 ≡ 2 ^ n + 0 [MOD 3]:= by exact Nat.ModEq.add h1 h2
  simp at h1

  -- Define k = 1002, so that n = 2*k (since 2004 = 2*1002)
  set k:= 1002 with hk
  clear_value k
  replace hk : n = 2 * k:= by linarith
  clear hn
  subst n

  -- Rewrite 2^(2*k) as (2^2)^k = 4^k
  rw [show 2 ^ (2 * k) = (2 ^ 2) ^ k by exact Nat.pow_mul 2 2 k] at h1
  simp at h1

  -- Establish that 4 ≡ 1 (mod 3)
  replace h2 : 4 ≡ 1 [MOD 3]:= by rfl
  -- Therefore 4^k ≡ 1^k ≡ 1 (mod 3)
  replace h2 : 4 ^ k ≡ 1 ^ k [MOD 3]:= by exact Nat.ModEq.pow k h2
  simp at h2

  -- Combine results to show 2003^(2*k) + 3 ≡ 1 (mod 3)
  replace h1 : 2003 ^ (2 * k) + 3 ≡ 1 [MOD 3]:= by exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm h2)) (id (Nat.ModEq.symm h1)))

  -- Prove that m > 0 and m ≥ 1
  have g1 : m > 0:= by subst m ; positivity
  replace g1 : m ≥ 1:= by omega
  rw [←hm] at h1

  -- Since m ≡ 1 (mod 3), we can write m = 3*t + 1 for some t
  replace h1 : 3 ∣ m - 1:= by exact (Nat.modEq_iff_dvd' g1).mp (id (Nat.ModEq.symm h1))
  rcases h1 with ⟨t, ht⟩
  replace ht : m = 3 * t + 1:= by omega
  clear hm g1
  subst m

  -- Simplify the expression using the form m = 3*t + 1
  ring_nf
  rw [show t * 3 = 3 * t by omega]
  -- Use the property (a^b)^c = a^(b*c)
  rw [show 2005 ^ (3 * t) = (2005 ^ 3) ^ t by exact Nat.pow_mul 2005 3 t]
  simp

  -- Calculate 2005^3 = 8060150125 and show it's ≡ 1 (mod 9)
  have g1 : 8060150125 ≡ 1 [MOD 9]:= by rfl
  -- Therefore (2005^3)^t ≡ 1^t ≡ 1 (mod 9)
  replace g1 : 8060150125 ^ t ≡ 1 ^ t [MOD 9]:= by  exact Nat.ModEq.pow t g1
  simp at g1
  set l:= 8060150125
  clear_value l

  -- Multiply both sides by 2005
  replace g1 : l ^ t * 2005 ≡ 1 * 2005 [MOD 9]:= by exact Nat.ModEq.mul g1 rfl
  simp at g1

  -- Finally, 2005 ≡ 7 (mod 9)
  have g2 : 2005 ≡ 7 [MOD 9]:= by rfl
  -- Therefore, our original expression is ≡ 7 (mod 9)
  exact Nat.ModEq.trans g1 g2
