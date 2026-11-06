import Mathlib

/-
## Subject II

Calculate the values of the natural numbers $\mathrm{a}, \mathrm{b}$, and $\mathrm{p}$, where $\mathrm{p}$ is a prime number, knowing that $a^{2}+a=p^{2^{b}}+2$.

Mathematical Gazette, E:14569
-/

theorem number_theory_102260 (a b p : ℕ) (hp : Nat.Prime p):
a^2+a = p^(2^b) +2 ↔ (a=2∧b=1∧p=2) := by 

  constructor
  
  intro h

  --Note that a^2+a = (a+1)*a is always even. We have p is even so p = 2.
  have pe : p = 2 := by
    have evenp: Even p := by 
      have : Even (a^2 + a) := by
        have : a^2 + a = a * (a+1) := by ring
        rw [this]
        exact Nat.even_mul_succ_self a
      by_contra note
      have : Odd p:= by exact Nat.not_even_iff_odd.mp note
      have : Odd (p^(2^b)) := by exact Odd.pow this
      have e2: Even 2 := by exact Nat.even_iff.mpr rfl
      have : Odd (p^(2^b)+2) := by exact Even.odd_add e2 this
      rw [← h] at this
      have : ¬ Even (a^2+a) := by exact Nat.not_even_iff_odd.mpr this
      contradiction
    exact (Nat.Prime.even_iff hp).mp evenp
  rw [pe] at h

  --Now we have (a+2)*(a-1) = 2^(2^b). We have that a has to be 2, since otherwise, both a+2 and a-1 have to be even, which is impossible.
  have apos : 0 < a := by 
    by_contra
    have a0 : a = 0 := by omega
    rw [a0] at h
    simp at h
  have : 0 ≤ a-1 := by omega
  have eq : (a+2)*(a-1) = 2^(2^b) := by 
    zify
    ring_nf at h ⊢
    field_simp at h ⊢
    nlinarith
  have d1 : a+2 ∣ 2^(2^b) := by use (a-1); omega
  have d2 : a-1 ∣ 2^(2^b) := by use (a+2); linarith
  have : Nat.Prime 2 := by trivial
  have hd1 := (Nat.dvd_prime_pow Nat.prime_two).mp d1
  have hd2 := (Nat.dvd_prime_pow Nat.prime_two).mp d2
  obtain ⟨k1, k1le,hk1⟩ := hd1
  obtain ⟨k2, k2le,hk2⟩ := hd2
  have : 2 ≤ k1 := by 
    by_contra 
    have k1le1: k1 ≤ 1 := by omega
    have : 2^k1 ≤ 2^1 := by refine Nat.pow_le_pow_of_le ?_ k1le1; norm_num
    simp at this
    linarith
  have : Even (a+2) := by 
    use 2^(k1-1)
    rw [←mul_two]
    rw [←pow_succ]
    have : k1-1+1 = k1 := by omega
    rw [this]
    exact hk1
  have : k2 = 0 := by 
    by_contra 
    have : 1 ≤ k2 := by omega
    have eam1 : Even (a-1) := by 
      use 2^(k2-1)
      rw [←mul_two]
      rw [←pow_succ]
      have : k2-1+1 = k2 := by omega
      rw [this]
      exact hk2
    have addto: a - 1 + 1 = a := by omega
    have : Odd 1 := by use 0; simp
    have : Odd a := by 
      rw [←addto]
      apply Even.add_odd;
      exact eam1
      exact this
    have e2: Even 2 := by use 1
    have : Odd (a+2) := by exact Even.odd_add e2 this
    have : ¬ Even (a+2) := by exact Nat.not_even_iff_odd.mpr this
    contradiction
  rw [this] at hk2
  simp at hk2
  have ae: a = 2 := by omega

  --Plug in the value of a and p. We get b = 1.
  rw [ae] at eq
  have be : b = 1 := by 
    field_simp at eq
    ring_nf at eq
    have : 4 = 2^2 := by norm_num
    rw [this] at eq
    have : 2 = 2^b := by 
      by_contra hhh
      by_cases ble1 : 2^b < 2
      have : 2^(2^b) < 2^2 := by refine Nat.pow_lt_pow_of_lt ?_ ble1; norm_num
      linarith
      have bge: 2 < 2^b := by 
        push_neg at hhh ble1
        exact Nat.lt_of_le_of_ne ble1 hhh
      have : 2^2 < 2^(2^b) := by refine Nat.pow_lt_pow_of_lt ?_ bge; norm_num
      linarith
    symm at this
    rw [Nat.pow_eq_self_iff] at this
    exact this
    norm_num
  tauto
      

  --For the other direction, just simple calculation.
  intro ⟨ae,be,pe⟩
  simp [ae,be,pe]