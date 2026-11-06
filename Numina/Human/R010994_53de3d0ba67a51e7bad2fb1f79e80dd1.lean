import Mathlib

/-
## Task A-2.3.

Determine all triples of prime numbers $(p, q, r)$ for which

$$
p^{q}=r-1
$$
-/

theorem number_theory_215307 (p q r : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)  (h : p ^ q = r - 1) : p = 2 ∧ q = 2 ∧ r = 5 := by

  have pge2 : 2 ≤ p := Nat.Prime.two_le hp
  have qge2 : 2 ≤ q := Nat.Prime.two_le hq
  have rge2 : 2 ≤ r := Nat.Prime.two_le hr

  --By checking the parity, we have that r has to be odd and p has to be even, so p = 2.
  have oddr : Odd r := by 
    by_contra noddr
    have evenr : Even r := by exact Nat.not_odd_iff_even.mp noddr
    have re : r=2 := by exact (Nat.Prime.even_iff hr).mp evenr
    rw [re] at h;
    simp at h
    have : 4 ≤ p^q := by 
      have : p^2 ≤ p^q := by exact Nat.pow_le_pow_of_le pge2 qge2
      have : 2^2 ≤ p^2 := by exact Nat.pow_le_pow_of_le_left pge2 2
      linarith
    linarith
  have evenrm1 : Even (r-1) := by refine Nat.Odd.sub_odd oddr ?_; exact Nat.odd_iff.mpr rfl

  have pe : p = 2 := by
    have evenp : Even p := by 
      by_contra nevenp
      have oddp : Odd p := by exact Nat.not_even_iff_odd.mp nevenp
      have oddpq : Odd (p^q) := by exact Odd.pow oddp
      have : Odd (r-1) := by rw [←h]; exact oddpq
      have : ¬ Even (r-1) := by exact Nat.not_even_iff_odd.mpr this
      contradiction
    exact (Nat.Prime.even_iff hp).mp evenp
  
  --If q = 2, then we must have r = 5.
  by_cases qe : q = 2 
  simp [pe,qe] at h
  omega

  --For q > 2, then we will have 3 ∣ r, but then r = 3 and we have a contradiction.
  exfalso
  have eq' : p^q + 1 = r := by omega
  rw [pe] at eq'
  have oddq : Odd q := by exact Nat.Prime.odd_of_ne_two hq qe
  have d3 : 3 ∣ 2 ^ q + 1:= by 
    have : 2 ≡ -1 [ZMOD 3] := by decide
    have con: 2^q ≡ (-1)^q [ZMOD 3] := by exact Int.ModEq.pow q this
    have : (-1)^q = -1 := by exact Odd.neg_one_pow oddq
    rw [this] at con
    have : 2^q + 1 ≡ (-1) + 1 [ZMOD 3] := by exact Int.ModEq.add con rfl
    simp at this
    refine Nat.dvd_of_mod_eq_zero ?_
    zify
    exact this
  rw [eq'] at d3
  have re: r = 3 := by 
    rw [Nat.prime_dvd_prime_iff_eq] at d3;
    symm
    exact d3
    norm_num
    exact hr
  rw [re] at eq'
  have qe : q = 1 := by 
    have: 2^q = 2 := by linarith
    rw [Nat.pow_eq_self_iff] at this
    exact this
    linarith
  rw [qe] at hq
  absurd hq; exact Nat.not_prime_one

    
    