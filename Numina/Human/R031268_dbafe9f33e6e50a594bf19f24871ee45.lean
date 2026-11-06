import Mathlib

/-
6. How many pairs of prime (not necessarily distinct) numbers ( $p ; q$) exist such that $p^{q}-p q$ is also prime? Answers:

A) at least one (+) B) at least two (+) C) at least three (-) D) none (-) E) infinitely many (-)
-/

theorem number_theory_211977 : {(p, q) : ℕ × ℕ | p.Prime ∧ q.Prime ∧ (p ^ q - p * q).Prime}.ncard = 2 := by 
  
  --We prove that the only case for (p,q) can be (2,3) or (3,2).
  let S := {(p, q) : ℕ × ℕ | p.Prime ∧ q.Prime ∧ (p ^ q - p * q).Prime}
  have : S = {(2,3),(3,2)} := by 
    ext ⟨p,q⟩ 

    constructor
    
    --First direction: assume we have a pair (p,q) in S.
    --We rewrite our equation and get p ∣ p^q-p*q
    --Since both are prime, we have p = p^q-p*q, so p^(q-1) = q + 1
    intro h
    simp [S] at h
    simp
    obtain ⟨pp,qp,h⟩ := h
    have pge2: 2 ≤ p := by exact Nat.Prime.two_le pp
    have qge2: 2 ≤ q := by exact Nat.Prime.two_le qp
    have pqpqge2 : 2 ≤ p^q - p*q := by exact Nat.Prime.two_le h

    have myeq: p^(q-1) = q + 1 := by 
      have : p ∣ (p^q - p*q) := by 
        have t1: p ∣ p^q := by 
          refine Dvd.dvd.pow ?_ ?_; 
          use 1; ring
          linarith
        have t2: p ∣ p*q := by use q
        exact Nat.dvd_sub' t1 t2
      have t2: p = p^q - p * q := by exact (Nat.prime_dvd_prime_iff_eq pp h).mp this
      have t3: p^q = p*q + p := by omega
      have : p^q = p^(q-1)*p := by 
        rw [←pow_succ]
        have : q-1+1 = q := by omega
        rw [this]
      rw [this] at t3
      rw [mul_comm] at t3
      have : p*q + p = p * (q+1) := by ring
      rw [this] at t3
      have : p≠ 0 := by linarith
      apply mul_left_cancel₀ this t3

    --From the above equation, we have that exactly one of p, q is even, so it's 2.
    --The claim then follows from a simple case analysis.
    have par: (Even p ∧ Odd q) ∨ (Odd p ∧ Even q) := by 
      have : Even p ∨ Odd p := by exact Nat.even_or_odd p
      
      rcases this with ep | op
      have : Even (p^(q-1)) := by refine (Nat.even_pow' ?_).mpr ep; omega
      have eqp1: Even (q+1) := by rw [← myeq]; exact this
      have oq: Odd q := by 
        by_contra t
        have: Even q := by exact Nat.not_odd_iff_even.mp t
        have : Odd (q+1) := by exact Even.add_one this
        have : ¬ Even (q+1) := by exact Nat.not_even_iff_odd.mpr this
        contradiction
      tauto

      have : Odd (p^(q-1)) := by exact Odd.pow op
      have : Odd (q+1) := by rw [←myeq]; exact this
      have : Even q := by 
        by_contra t
        have : Odd q := by exact Nat.not_even_iff_odd.mp t
        have : Even (q+1) := by exact Odd.add_one this
        have : ¬ Odd (q+1) := by exact Nat.not_odd_iff_even.mpr this
        contradiction
      tauto

    rcases par with epoq | opeq
    obtain ⟨ep, oq⟩ := epoq
    have pe2: p = 2 := by exact (Nat.Prime.even_iff pp).mp ep
    rw [pe2] at myeq
    have : q ≤ 3 := by 
      have : ∀ m : ℕ, 2^(m+4 - 1) > m+4+1 := by 
        intro m
        induction' m with m hm
        simp

        have : 2 ^ (m + 1 + 4 - 1) = 2 * 2 ^ (m + 4 - 1) := by 
          field_simp
          rw [pow_succ]
          ring
        rw [this]
        have : m+1+4+1 ≤ 2*(m+4+1) := by omega
        linarith
      by_contra 
      have qge4 : 4 ≤ q := by omega
      have exi : ∃ m : ℕ, m + 4 = q := by use q-4; omega
      obtain ⟨m,hm⟩ := exi
      specialize this m
      rw [hm] at this
      linarith
    by_cases qe2 : q = 2 
    exfalso
    rw [qe2] at oq
    have : Even 2 := by use 1
    contradiction
    have : q = 3 := by omega
    left; tauto

    obtain ⟨op,eq⟩ := opeq
    have qe2: q = 2 := by exact (Nat.Prime.even_iff qp).mp eq
    rw [qe2] at myeq
    norm_num at myeq
    right
    tauto




    intro h
    simp at h
    simp [S]
    
    rcases h with ⟨pe,qe⟩ | ⟨pe,qe⟩
    simp [pe,qe]
    norm_num
    simp [pe,qe]
    norm_num

  have : S.ncard = 2 := by rw[this]; simp
  simp [S] at this
  exact this