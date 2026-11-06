import Mathlib

theorem algebra_184166 :
    {n : ℤ | (n^2 - 4) ≠ 0 ∧ (n^2 + 2 * n - 8) % (n^2 - 4) = 0} = {n : ℤ | n = -1 ∨ n=-3 ∨ n=0 ∨ n = -4} := by 

    ext n
    
    constructor

    simp
    intro nu h

    have : n ≠ 2 := by
      by_contra ne2
      rw [ne2] at nu
      norm_num at nu
    have : n ≠ -2 := by
      by_contra nem2
      rw [nem2] at nu
      norm_num at nu
    have nm2: n-2 ≠ 0 := by omega

    --We rewrite the assumption to get that n-2 divides 2, so n-2 can only be ±1 or ±2.
    --Hence n = -1 or -3 or 0 or -4.
    have t1 : n^2 - 4 = (n+2)*(n-2) := by ring
    rw [t1] at h
    have t2: n^2 + 2*n - 8 = (n+4)*(n-2) := by ring
    rw [t2] at h
    obtain ⟨k,hk⟩ := h
    have d2: (n+2) ∣ (n+4) := by 
      use k
      rw [mul_comm] at hk
      nth_rw 3 [mul_comm] at hk
      rw [mul_assoc] at hk
      apply mul_left_cancel₀ at hk
      exact hk
      exact nm2
    have dd: n+2 ∣ 2 := by 
      have : n+2 ∣ n+2 := by exact Int.dvd_refl (n + 2)
      have : n+2 ∣ (n+4) - (n+2) := by exact Int.dvd_sub d2 this
      field_simp at this
      norm_num at this
      exact this

    by_cases np2p: 0 ≤ n+2
    let n' : ℕ := (n+2).toNat
    have : n' = n+2 := by omega
    have : n' ∣ 2 := by 
      obtain ⟨k,hk⟩ := dd
      use k.toNat
      have : 0 ≤ k := by nlinarith
      have : k = k.toNat := by omega
      nlinarith
    have p2: Nat.Prime 2 := by norm_num
    have : n' = 1 ∨ n' = 2 := by exact (Nat.dvd_prime p2).mp this
    simp [n'] at this
    omega

    have np2n: n+2 < 0 := by linarith
    let n' : ℕ := (-(n+2)).toNat 
    have : n' = -(n+2):= by omega
    have : n' ∣ 2 := by
      obtain ⟨k,hk⟩ := dd
      use (-k).toNat
      have : k < 0 := by nlinarith
      have : (-k).toNat = -k := by omega
      nlinarith
    have p2: Nat.Prime 2 := by norm_num
    have : n' = 1 ∨ n' = 2 := by exact (Nat.dvd_prime p2).mp this
    simp [n'] at this
    omega

    --We check that all these four numbers work.
    simp
    intro h
    rcases h with h|h|h|h
    rw [h]; norm_num
    rw [h]; norm_num
    rw [h]; norm_num
    rw [h]; norm_num