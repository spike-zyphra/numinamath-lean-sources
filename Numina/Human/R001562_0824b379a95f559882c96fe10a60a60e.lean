import Mathlib

open Real List

/- 1. (BUL 1) Prove that all numbers in the sequence  $$ \frac{107811}{3}, \frac{110778111}{3}, \frac{111077781111}{3}, \ldots $$  are perfect cubes. -/

--Lemma 1, 3 divides 999..99.
lemma l1 (n:ℕ): 3 ∣ 10^(n+1) - 1 := by 
  induction' n with n hn
  
  simp
  use 3

  obtain ⟨d,hd⟩ := hn
  use (10*d+3)
  rw [pow_succ]

  have : 1 ≤ 10^(n+1) := by exact Nat.one_le_pow' (n + 1) 9
  have : 10 ^ (n + 1) = 3*d + 1 := by omega
  rw [this]
  omega

--Lemma 2 and 3 are for 11...11 and 77...77. Simple induction.
lemma l2 (n : ℕ):
  @Nat.ofDigits ℝ Ring.toSemiring 10 (replicate (n) 1) = ((10^n-1)/9) := by
  
  induction' n with n hn
  simp
  norm_cast

  have : replicate (n + 1) 1 = 1 :: replicate n 1 := by
    exact rfl
  rw [this]
  norm_cast
  rw [Nat.ofDigits_cons]
  norm_cast at hn
  simp
  rw [hn]
  rify
  ring_nf
  
lemma l3 (n : ℕ):
  @Nat.ofDigits ℝ semiring 10 (replicate n 7) = ((10^n-1)/(9:ℝ)) * 7 := by
  
  induction' n with n hn
  simp
  norm_cast

  have : replicate (n + 1) 7 = 7 :: replicate n 7 := by
    exact rfl
  rw [this]
  norm_cast
  rw [Nat.ofDigits_cons]
  norm_cast at hn
  simp
  rw [hn]
  rify
  ring_nf


theorem number_theory_24605 
(a : ℕ → ℝ)
(
ha: ∀ n, a n = 
(
Nat.ofDigits (10) ((replicate (n+2) 1) ++ [8] ++ (replicate (n+1) 7) ++ [0] ++ (replicate (n+1) 1))
)
/ (3 : ℝ)
):
  ∀ n, ∃ m:ℕ, a n = m^3 := by 

  intro n
  specialize ha n

  --We rewrite the expression of a n by numbers using the property of ofDigits.
  have eq : Nat.ofDigits (10) ((replicate (n+2) 1) ++ [8] ++ (replicate (n+1) 7) ++ [0] ++ (replicate (n+1) 1)) = 
  (10^(3*(n+1)+3) - 10^(2*(n+1)+3)) / (9:ℝ) + 7 * ( (10^(2*(n+1)+2) - 10^(n+1+1)) / (9:ℝ)) +  (10^(n+1+2)-1)/ (9:ℝ):= by 
    norm_cast
    rw [Nat.ofDigits_append]
    rw [Nat.ofDigits_append]
    rw [Nat.ofDigits_append]
    rw [Nat.ofDigits_append]
    simp
    rify

    have t1: Nat.ofDigits 10 (replicate (n + 2) 1) = (10^(n + 2)-1) / (9:ℝ) := by apply l2 (n+2)
    have t2: @Nat.ofDigits ℝ semiring 10 (replicate (n + 1) 7) = (10^(n + 1)-1) / (9:ℝ) * 7 := by apply l3 (n+1)
    have t3: Nat.ofDigits 10 (replicate (n + 1) 1) = (10^(n + 1)-1) / (9:ℝ) := by apply l2 (n+1)
    rw [t1,t2,t3]
    field_simp
    ring_nf

  rw [eq] at ha

  --We have a n = ( (10^(n+2)-1)/3 ) ^3.
  have eq2: a n = (10^(3*(n+1)+3) - 3*10^(2*(n+1)+2) + 3*10^(n+1+1) -1) / (27:ℝ) := by 
    rw [ha]
    field_simp
    ring_nf
  have eq3: a n = ((10^(n+1+1) - 1) / (3:ℝ))^3 := by 
    rw [eq2]
    ring_nf
  
  have dd : (3:ℕ) ∣ (10^(n+1+1) - 1) := by 
    apply l1

  --Let m = (10^(n+2)-1)/3. We get our claim.
  obtain ⟨m,hm⟩ := dd
  use m
  have eq4: @Nat.cast ℝ instNatCast m = (10^(n+1+1) - 1) / (3:ℝ) := by 
    rify at hm
    field_simp at hm ⊢
    rw [hm]
    ring
  
  rw [eq4]
  exact eq3
