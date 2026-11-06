import Mathlib

/-
$a$, $b$, $c$ are three distinct natural numbers, pairwise coprime. It is known that the sum of any two of them can be divided by the third. Then ${{a}^{3}}+{{b}^{3}}+{{c}^{3}}=$ ___          ___ .
-/

theorem number_theory_626939 (a b c : ℕ) (dab: a≠b) (dbc:b≠c) (dac:a≠c)
(pab: Nat.Coprime a b) (pbc: Nat.Coprime b c) (pca: Nat.Coprime c a) (h :a ∣ b+c ∧ b ∣ a+c ∧ c ∣ a+b): a^3 + b^3 + c^3 = 36 := by

  --Wlog we can assume that a < b < c.
  wlog alb : a < b
  have bla: b < a := by omega
  have : b^3 + a^3 + c^3 = 36 := by 
    apply this
    symm; exact dab
    omega
    exact dbc
    exact pab.symm
    exact pca.symm
    exact pbc.symm
    nth_rw 3 [add_comm]
    tauto
    exact bla
  omega
  wlog blc : b < c
  by_cases alc : a < c
  have clb : c < b := by omega
  have : a^3 + c^3 + b^3 = 36 := by
    apply this
    exact dac
    exact dbc.symm
    exact dab
    exact pca.symm
    exact pbc.symm
    exact pab.symm
    nth_rw 1 [add_comm]
    tauto
    exact alc
    exact clb
  omega
  have cla : c < a := by omega
  have : c^3 + a^3 + b^3 = 36 := by
    apply this
    exact dac.symm
    exact dab
    exact dbc.symm
    exact pca
    exact pab
    exact pbc
    nth_rw 2 [add_comm]
    nth_rw 3 [add_comm]
    tauto
    exact cla
    exact alb
  omega

  --Since c ∣ a+b, we have c = a + b.
  obtain ⟨adbc, bdac,cdab⟩ := h
  obtain ⟨n,hn⟩ := cdab
  have ne: n = 1 := by 
    have : n ≤ 1 := by nlinarith
    have : 0 < n := by nlinarith
    omega
  rw [ne] at hn; simp only [one_mul, mul_one] at hn
  
  --Since b ∣ a+c, we have 2*b = a+c.
  obtain ⟨m,hm⟩ := bdac
  have : m = 2 := by nlinarith
  rw [this] at hm

  --Then we have b=2a and c=3a. Since a,b,c are pairwise coprime, we have a = 1 and then b = 2, c = 3.
  have : b = 2*a := by omega
  have : c = 3*a := by omega
  have adv : a ∣ b := by use 2; linarith
  have ada : a ∣ a := by exact dvd_refl a
  have adgcd: a ∣ b.gcd a := by exact Nat.dvd_gcd adv ada
  have : b.gcd a = 1 := by exact Nat.coprime_comm.mp pab
  rw [this] at adgcd
     
  have ae : a = 1 := by exact Nat.eq_one_of_dvd_one adgcd
  have be : b = 2 := by omega
  have ce : c = 3 := by omega

  rw [ae,be,ce]
  norm_num