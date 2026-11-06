import Mathlib

/-
Let $k$ be a positive integer. Determine the list of binary digits of the number $2^k - 1$, where the digits are ordered from most significant to least significant. Show that this list has length $k$ and all its elements are 1.
-/

--A lemma about the digits about 2*m+1.
lemma l1 (m:ℕ):
Nat.digits 2 (2*m+1) = 1 :: Nat.digits 2 m := by 
  have : 2*m+1 = 1 + 2*m := by ring
  rw [this]
  rw [Nat.digits_add]
  all_goals simp

theorem number_theory_636896 (k:ℕ) (kpos: 0 < k): (Nat.digits 2 (2 ^ k - 1)).length = k ∧ ∀ d ∈ Nat.digits 2 (2 ^ k - 1), d = 1 := by 

  --We prove this by induction and use our lemma.
  have cla : ∀ n:ℕ, (Nat.digits 2 (2 ^ (n+1) - 1)).length = (n+1) ∧ ∀ d ∈ Nat.digits 2 (2 ^ (n+1) - 1), d = 1 := by
    intro n
    induction' n with n hn

    simp

    --Using our lemma, we have that when m becomes 2*m+1, the length increase by 1 and the extre digit is 1.
    obtain ⟨h1,h2⟩ := hn
    have : Nat.digits 2 (2 ^ (n + 1 + 1) - 1) = 1 :: Nat.digits 2 (2 ^ (n + 1) - 1) := by 
      have : 2^(n+1+1)-1 = 2*(2^(n+1)-1)+1 := by 
        nth_rw 1 [pow_succ]
        zify
        have : @Nat.cast ℤ AddMonoidWithOne.toNatCast (2 ^ (n + 1) - 1) = 2^(n+1) -1 := by 
          have : 1 ≤ @HPow.hPow ℕ ℕ ℕ instHPow 2 (n + 1) := by exact Nat.one_le_two_pow
          norm_cast
        rw [this]
        have : @Nat.cast ℤ instNatCastInt (2 ^ (n + 1) * 2 - 1)  = 2^(n+1)*2 -1 := by 
          have: 1 ≤ 2 ^ (n + 1) * 2 := by 
            have : 1 ≤ 2^(n+1) := by exact Nat.one_le_two_pow
            linarith
          norm_cast
        rw [this]
        ring
      rw [this]
      apply l1
    rw [this]

    constructor

    simp at h1 ⊢
    exact h1

    intro d hd
    simp at h2 hd
    rcases hd with hd | hd
    exact hd
    exact h2 d hd


  have exi : ∃ n:ℕ, n+1 = k:= by use k-1; omega
  obtain ⟨n,hn⟩ := exi
  specialize cla n
  rw [hn] at cla
  exact cla
  