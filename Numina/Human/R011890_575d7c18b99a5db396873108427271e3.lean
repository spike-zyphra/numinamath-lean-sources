import Mathlib

/- Find all primes that can be written both as a sum and as a difference of two primes (note that $ 1$ is not a prime). -/

theorem number_theory_63769 {p : ℕ} (hp : Nat.Prime p) :
(∃ q r s t : ℕ, Nat.Prime q ∧ Nat.Prime r ∧ Nat.Prime s ∧ Nat.Prime t ∧ p = q + r ∧ p = s - t) 
↔
p = 5 := by 
  
  constructor

  intro h
  obtain ⟨q,r,s,t,hq,hr,hs,ht,h⟩ :=  h

  wlog rleq : r ≤ q
  have qler : q ≤ r := by omega
  apply this
  exact hp
  exact hr
  exact hq
  exact hs
  exact ht
  omega
  exact qler

  have pge2 : 2 ≤ p := by exact Nat.Prime.two_le hp
  have qge2 : 2 ≤ q := by exact Nat.Prime.two_le hq
  have rge2 : 2 ≤ r := by exact Nat.Prime.two_le hr
  have sge2 : 2 ≤ s := by exact Nat.Prime.two_le hs
  have tge2 : 2 ≤ t := by exact Nat.Prime.two_le ht

  -- p cannot be 2, since otherwise there is no choice for q and r. Hence, p is odd.
  have pge3 : 3 ≤ p := by
    by_contra pl3
    push_neg at pl3
    have pe : p = 2 := by omega
    rw [pe] at h
    linarith only [qge2,rge2, h]
  have oddp : Odd p := by 
    have : ¬ p = 2 := by linarith only [pge3]
    exact Nat.Prime.odd_of_ne_two hp this

  --Then, one of q and r is even, and one of s and t is even.
  --We have r = 2 and t = 2.
  have re : r = 2 := by 
    by_contra rne2
    have oddr : Odd r := by exact Nat.Prime.odd_of_ne_two hr rne2
    have oddq : Odd q := by 
      have : 2 < r := by omega
      have : 2 < q := by omega
      have : ¬ q = 2 := by linarith only [this]
      exact Nat.Prime.odd_of_ne_two hq this
    have evenp : Even p := by 
      rw [h.left]
      exact Odd.add_odd oddq oddr
    have noddp : ¬ Odd p := by exact Nat.not_odd_iff_even.mpr evenp
    contradiction
  have te : t = 2 := by 
    have : t < s := by omega
    by_contra tne2
    have oddt : Odd t := by exact Nat.Prime.odd_of_ne_two ht tne2
    have odds : Odd s := by 
      have : 2 < t := by omega
      have : 2 < s := by omega
      have : ¬ s = 2 := by linarith only [this]
      exact Nat.Prime.odd_of_ne_two hs this
    have evenp : Even p := by 
      rw [h.right]
      exact Nat.Odd.sub_odd odds oddt
    have noddp : ¬ Odd p := by exact Nat.not_odd_iff_even.mpr evenp
    contradiction
  
  rw [re,te] at h

  --Considering mod 3, we get that q % 3 must be 0, so q = 3. Hence, we get p = 5.
  have peqp2 : p = q + 2 := h.left
  have seqp4 : s = q + 4 := by omega
  have qe : q = 3 := by 
    have d3q : 3 ∣ q := by 
      have d3qm0 : q % 3 = 0 := by 
        by_contra d3qnm0
        by_cases d3qm1 : q % 3 = 1
        have : p % 3 = 0 := by rw [peqp2]; omega
        have d3p: 3 ∣ p := by exact Nat.dvd_of_mod_eq_zero this
        have : Nat.Prime 3 := by decide
        have pe: p = 3 := by exact Eq.symm ((fun {p q} pp qp => (Nat.prime_dvd_prime_iff_eq pp qp).mp) this hp d3p)
        linarith only [pe,peqp2,qge2]
        have d3qm2 : q % 3 = 2 := by omega
        have : s % 3 = 0 := by rw [seqp4]; omega
        have d3p: 3 ∣ s := by exact Nat.dvd_of_mod_eq_zero this
        have : Nat.Prime 3 := by decide
        have se: s = 3 := by exact Eq.symm ((fun {p q} pp qp => (Nat.prime_dvd_prime_iff_eq pp qp).mp) this hs d3p)
        have pe : p = 1 := by omega
        linarith [pe,pge2]
        
      exact Nat.dvd_of_mod_eq_zero d3qm0
    have : Nat.Prime 3 := by decide
    exact Eq.symm ((fun {p q} pp qp => (Nat.prime_dvd_prime_iff_eq pp qp).mp) this hq d3q)
  rw [qe] at h
  linarith only [h]

  --For the other direction, simple calculation.
  intro pe
  use 3, 2, 7, 2
  simp [pe]
  norm_num