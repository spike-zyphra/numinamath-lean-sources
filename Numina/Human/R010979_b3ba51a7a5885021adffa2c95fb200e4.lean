import Mathlib

/-
14.4.27 ** Find all prime numbers that can be expressed both as the sum of two prime numbers and as the difference of two prime numbers.
-/

theorem number_theory_212714 (p : ℕ) (hp : p.Prime): 
(∃a:ℕ, ∃b:ℕ, (a.Prime ∧ b.Prime ∧ p = a + b)) ∧ (∃c:ℕ, ∃d:ℕ, (c.Prime ∧ d.Prime ∧ p = c- d)) 
↔  
p = 5 := by
  
  constructor
  
  --From left to right.
  intro ⟨h1,h2⟩ 

  obtain ⟨a,b,ap,bp,hab⟩ := h1
  --Wlog we can assume that a ≤ b.
  wlog aleb : a ≤ b
  have blea: b ≤ a := by omega
  apply this
  exact hp
  exact h2
  exact bp
  exact ap
  omega
  exact blea

  --We have a = 2 by checking the parity and a and b.
  have ae : a = 2 := by 
    by_contra anne2
    have : 2 ≤ a := by exact Nat.Prime.two_le ap
    have : 2 < a := by omega
    have : 2 < b := by omega
    have : ¬ b = 2 := by omega
    have oa : Odd a := by exact Nat.Prime.odd_of_ne_two ap anne2
    have ob : Odd b := by exact Nat.Prime.odd_of_ne_two bp this
    have : Even p := by
      have : Even (a+b) := by exact Odd.add_odd oa ob
      rw [← hab] at this
      exact this
    have : p = 2 := by exact (Nat.Prime.even_iff hp).mp this
    omega

  obtain ⟨c,d,cp,dp,hcd⟩ := h2
  --We have d = 2 by checking the parity and c and d.
  have de : d = 2 := by 
    by_contra dne2
    have : 2 ≤ d := by exact Nat.Prime.two_le dp
    have : 2 < d := by omega
    have : 2 < c := by omega
    have : ¬ c=2 := by omega
    have oc : Odd c := by exact Nat.Prime.odd_of_ne_two cp this
    have od : Odd d := by exact Nat.Prime.odd_of_ne_two dp dne2
    have : Even p := by 
      have : Even (c-d) := by exact Nat.Odd.sub_odd oc od
      rw [← hcd] at this
      exact this
    have : p = 2 := by exact (Nat.Prime.even_iff hp).mp this
    omega
  
  rw [ae] at hab
  rw [de] at hcd

  rw [add_comm] at hab
  have cebp4: c = b + 4 := by omega

  --Then, b, b+2, b+4 are all prime numbers. The only possibilities is b = 3.
  have be : b = 3 := by 
    
    by_cases bm1 : b % 3 = 1
    have : (b+2)%3 = 0 := by omega
    rw [←hab] at this
    have d3p: 3 ∣ p := by exact Nat.dvd_of_mod_eq_zero this
    have pe: p = 3 := by rw [Nat.Prime.dvd_iff_eq] at d3p; exact d3p; exact hp; norm_num
    rw [pe] at hab
    have : b = 1 := by linarith
    rw [this] at bp
    norm_num at bp

    by_cases bm2 : b % 3 = 2
    have : (b+4)%3 = 0 := by omega
    rw [← cebp4] at this
    have d3c : 3 ∣ c := by exact Nat.dvd_of_mod_eq_zero this
    have ce : c = 3 := by 
      rw [Nat.Prime.dvd_iff_eq] at d3c
      exact d3c
      exact cp
      norm_num
    have : p = 1 := by linarith
    rw [this] at hp
    norm_num at hp

    have b3d : b % 3 = 0 := by omega
    have : 3 ∣ b := by exact Nat.dvd_of_mod_eq_zero b3d
    have : b = 3 := by 
      rw [Nat.Prime.dvd_iff_eq] at this; 
      exact this
      exact bp
      norm_num
    assumption
  
  linarith

  --From right to left
  --Just let a=2, b=3, c=7, d=2.
  intro pe
  constructor
  use 2,3
  simp [pe]
  norm_num
  use 7,2
  simp [pe]
  norm_num


