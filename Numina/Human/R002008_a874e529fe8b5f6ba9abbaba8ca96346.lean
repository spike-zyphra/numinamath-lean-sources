import Mathlib

/- Find prime numbers $p , q , r$  such that $p+q^2+r^3=200$. Give all the possibilities.

Remember that the number $1$ is not prime. -/
theorem number_theory_54583 (p q r : ℕ): 
p.Prime ∧ q.Prime ∧ r.Prime ∧ (p + q^2 + r^3 = 200) 
↔ 
(p = 167 ∧ q = 5 ∧ r = 2) ∨ (p = 71 ∧ q = 11 ∧ r = 2) ∨ (p = 23 ∧ q = 13 ∧ r = 2) ∨ (p = 71 ∧ q = 2 ∧ r = 5) := by
  
  constructor


  --From left to right, assume we have p,q,r primes and their sum equal to 200.
  intro ⟨pp,qp,rp,h⟩ 

  --Some general bounds on p, q, and r.
  have pge2 : 2 ≤ p := by exact Nat.Prime.two_le pp
  have qge2 : 2 ≤ q := by exact Nat.Prime.two_le qp
  have rge2 : 2 ≤ r := by exact Nat.Prime.two_le rp
  have ple200 : p ≤ 200 := by omega
  have qle14 : q ≤ 15 := by 
    by_contra qg15
    push_neg at qg15
    have : 15^2 < q^2 := by nlinarith
    omega
  have rle : r ≤ 6 := by 
    by_contra rg6
    push_neg at rg6
    have : 6^3 < r^3 := by apply pow_lt_pow_left₀; exact rg6; norm_num; norm_num
    omega
  
  --Consider the parity, one of p,q,r has to be even, so it is 2.
  have : Even p ∨ Even q ∨ Even r := by
    by_contra allodd
    push_neg at allodd
    simp at allodd
    obtain ⟨op,oq,or⟩ := allodd
    have t1: Odd (q^2) := by exact Odd.pow oq
    have t2: Odd (r^3) := by exact Odd.pow or
    have t3: Even (p+q^2) := by exact Odd.add_odd op t1
    have t4: Odd (p+q^2 + r^3) := by exact Even.add_odd t3 t2
    rw [h] at t4
    have : ¬ Odd 200 := by decide
    contradiction
  
  --Now, we just enumerate all cases.
  obtain ep | eq | er := this
  -- Case p even:
  have pe : p = 2 := by exact (Nat.Prime.even_iff pp).mp ep
  simp [pe] at h ⊢
  interval_cases q <;> interval_cases r <;> norm_num at h ⊢

  -- Case q even:
  have qe : q = 2 := by exact (Nat.Prime.even_iff qp).mp eq
  simp [qe] at h ⊢
  interval_cases p <;> interval_cases r <;> norm_num at h pp rp ⊢

  
  -- Case r even:
  have re : r = 2 := by exact (Nat.Prime.even_iff rp).mp er
  simp [re] at h ⊢
  interval_cases p <;> interval_cases q <;> norm_num at h pp qp ⊢


  --From right to left, simple caculation shows they satisfy the equation.
  intro h
  obtain ⟨pe,qe,re⟩ | ⟨pe,qe,re⟩ | ⟨pe,qe,re⟩ | ⟨pe,qe,re⟩ := h <;>
  simp [pe,qe,re] <;>
  norm_num