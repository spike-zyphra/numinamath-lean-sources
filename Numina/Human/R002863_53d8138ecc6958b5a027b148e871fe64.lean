import Mathlib

/-
$3 \cdot 66$ What is the largest even number that cannot be expressed as the sum of two odd composite numbers?
(2nd American Invitational Mathematics Examination, 1984)
-/

--The last digit of an even number can only be 0, 2, 4, 6, 8.
lemma evendig (n:ℕ) (evenn : Even n):
n % 10 = 0 ∨ n % 10 = 2 ∨ n % 10 = 4 ∨ n % 10 = 6 ∨ n % 10 = 8 := by 
  obtain ⟨k,hk⟩ := evenn
  have lkm10 : 0 ≤ k % 10 := by exact Nat.zero_le (k % 10)
  have ukm10 : k % 10 < 10 := by refine Nat.mod_lt k ?_; norm_num
  interval_cases(k % 10)<;> omega

theorem number_theory_123408 :
IsGreatest {n : ℕ | Even n ∧ ¬ (∃ c1 c2 : ℕ, Odd c1 ∧ Odd c2 ∧ 2≤ c1 ∧ ¬ Nat.Prime c1 ∧ 2≤ c2 ∧ ¬ Nat.Prime c2 ∧ c1 + c2 = n)} 38 := by
  unfold IsGreatest upperBounds
  simp

  constructor

  -- Prove that 38 satisfies the conditions.
  constructor
  use 19

  --We check all the x and y such that x+y = 38.
  intro x oddx y oddy xge2 cx yge2 cy
  by_contra xpye
  wlog xley : x ≤ y
  have ylex : y ≤ x := by linarith
  apply this
  exact oddy
  exact oddx
  exact yge2
  exact cy
  exact xge2
  exact cx
  omega
  exact ylex

  have : x ≤ 19 := by omega
  interval_cases x <;>
  simp_all
  
  have : Nat.Prime 2 := by decide
  contradiction

  have : Nat.Prime 3 := by decide
  contradiction

  have : Even 4 := by use 2
  have : ¬ Odd 4 := by exact Nat.not_odd_iff_even.mpr this
  contradiction

  have : Nat.Prime 5 := by decide
  contradiction

  have :  Even 6 := by use 3
  have : ¬ Odd 6 := by exact Nat.not_odd_iff_even.mpr this
  contradiction

  have :  Nat.Prime 7 := by decide
  contradiction

  have :  Even 8 := by use 4
  have : ¬ Odd 8 := by exact Nat.not_odd_iff_even.mpr this
  contradiction

  have : y = 29 := by omega
  rw [this] at cy
  have : Nat.Prime 29 := by decide
  contradiction

  have : Even 10 := by use 5
  have : ¬ Odd 10 := by exact Nat.not_odd_iff_even.mpr this
  contradiction

  have :  Nat.Prime 11 := by decide
  contradiction

  have : Even 12 := by use 6
  have : ¬ Odd 12 := by exact Nat.not_odd_iff_even.mpr this
  contradiction

  have : Nat.Prime 13 := by decide
  contradiction

  have : Even 14 := by use 7
  have : ¬ Odd 14 := by exact Nat.not_odd_iff_even.mpr this
  contradiction

  have : y = 23 := by omega
  rw [this] at cy
  have : Nat.Prime 23 := by decide
  contradiction

  have : Even 16 := by use 8
  have : ¬ Odd 16 := by exact Nat.not_odd_iff_even.mpr this
  contradiction

  have : Nat.Prime 17 := by decide
  contradiction

  have : Even 18 := by use 9
  have : ¬ Odd 18 := by exact Nat.not_odd_iff_even.mpr this
  contradiction

  have : Nat.Prime 19 := by decide
  contradiction

  -- From right to left, we need to prove that 38 is the smallest one.
  intro k evenk h
  by_contra kg38; push_neg at kg38
  by_cases ke39 : k = 39
  rw [ke39] at evenk
  have : Odd 39 := by use 19; norm_num
  have : ¬ Even 39 := by exact Nat.not_even_iff.mpr rfl
  contradiction
  --Assume otherwise that k ≥ 40.
  have kge40 : 40 ≤ k := by omega

  --Then, the last digit of k can be 0, 2, 4, 6, or 8.
  --We check every case and give the value of x adn y which violate the condition.
  have : k % 10 = 0 ∨ k % 10 = 2 ∨ k % 10 = 4 ∨ k % 10 = 6 ∨ k % 10 = 8 := by apply evendig k; exact evenk
  rcases this with e0 | e2 | e4 | e6 | e8


  have d10k : 10 ∣ k := by exact Nat.dvd_of_mod_eq_zero e0
  obtain ⟨d,hd⟩ := d10k
  have : 4 ≤ d := by omega
  have exi : ∃ n, k = 15 + 5 * n := by 
    use (k-15)/5
    have : 5 * ((k - 15) / 5) = k-15 := by 
      refine Nat.mul_div_eq_iff_dvd.mpr ?_;
      refine Nat.dvd_sub ?_ ?_ ?_
      linarith
      use 2*d
      rw [hd]
      ring
      use 3
    rw [this]
    omega
  obtain ⟨l,hl⟩ := exi
  let x := 15
  let y := 5*l
  have eq : x + y = k := by omega
  have oddx: Odd x := by use 7; norm_num
  have xge2 : 2 ≤ x := by norm_num
  have nxprime : ¬ Nat.Prime x := by decide
  have oddy: Odd y := by 
    by_contra t
    have eveny : Even y := by exact Nat.not_odd_iff_even.mp t
    have : Odd (x+y) := by exact Even.odd_add eveny oddx
    have : ¬ Even (x+y) := by exact Nat.not_even_iff_odd.mpr this
    rw [eq] at this
    contradiction
  have : 2 ≤ y := by omega
  have nyprime : ¬ Nat.Prime y := by
    by_contra yp
    have d5: 5 ∣ y := by use l
    rw [Nat.dvd_prime] at d5
    obtain t1 | t2 := d5
    simp at t1
    omega
    exact yp
  have : ¬ x+y = k := by 
    apply h
    assumption
    assumption
    assumption
    assumption
    assumption
    assumption
  contradiction
    
  have d10k : 10 ∣ k-2 := by refine (Nat.modEq_iff_dvd' ?_).mp (id (Eq.symm e2)); linarith
  obtain ⟨d,hd⟩ := d10k
  have : 4 ≤ d := by omega
  have exi : ∃ n, k = 27 + 5 * n := by 
    use (k-27)/5
    have : 5 * ((k - 27) / 5) = k-27 := by 
      refine Nat.mul_div_eq_iff_dvd.mpr ?_;
      have : k - 27 = k - 2 - 25 := by omega
      rw [this]
      rw [hd]
      refine Nat.dvd_sub ?_ ?_ ?_
      omega
      use 2*d
      ring
      use 5
    rw [this]
    omega
  obtain ⟨l,hl⟩ := exi
  let x := 27
  let y := 5*l
  have eq : x + y = k := by omega
  have oddx: Odd x := by use 13; norm_num
  have xge2 : 2 ≤ x := by norm_num
  have nxprime : ¬ Nat.Prime x := by decide
  have oddy: Odd y := by 
    by_contra t
    have eveny : Even y := by exact Nat.not_odd_iff_even.mp t
    have : Odd (x+y) := by exact Even.odd_add eveny oddx
    have : ¬ Even (x+y) := by exact Nat.not_even_iff_odd.mpr this
    rw [eq] at this
    contradiction
  have : 2 ≤ y := by omega
  have nyprime : ¬ Nat.Prime y := by
    by_contra yp
    have d5: 5 ∣ y := by use l
    rw [Nat.dvd_prime] at d5
    obtain t1 | t2 := d5
    simp at t1
    omega
    exact yp
  have : ¬ x+y = k := by 
    apply h
    assumption
    assumption
    assumption
    assumption
    assumption
    assumption
  contradiction

  have d10k : 10 ∣ k-4 := by refine (Nat.modEq_iff_dvd' ?_).mp (id (Eq.symm e4)); linarith
  obtain ⟨d,hd⟩ := d10k
  have : 4 ≤ d := by omega
  have exi : ∃ n, k = 9 + 5 * n := by 
    use (k-9)/5
    have : 5 * ((k - 9) / 5) = k-9 := by 
      refine Nat.mul_div_eq_iff_dvd.mpr ?_;
      have : k - 9 = k - 4 - 5 := by omega
      rw [this]
      rw [hd]
      refine Nat.dvd_sub ?_ ?_ ?_
      omega
      use 2*d
      ring
      use 1
    rw [this]
    omega
  obtain ⟨l,hl⟩ := exi
  let x := 9
  let y := 5*l
  have eq : x + y = k := by omega
  have oddx: Odd x := by use 4; norm_num
  have xge2 : 2 ≤ x := by norm_num
  have nxprime : ¬ Nat.Prime x := by decide
  have oddy: Odd y := by 
    by_contra t
    have eveny : Even y := by exact Nat.not_odd_iff_even.mp t
    have : Odd (x+y) := by exact Even.odd_add eveny oddx
    have : ¬ Even (x+y) := by exact Nat.not_even_iff_odd.mpr this
    rw [eq] at this
    contradiction
  have : 2 ≤ y := by omega
  have nyprime : ¬ Nat.Prime y := by
    by_contra yp
    have d5: 5 ∣ y := by use l
    rw [Nat.dvd_prime] at d5
    obtain t1 | t2 := d5
    simp at t1
    omega
    exact yp
  have : ¬ x+y = k := by 
    apply h
    assumption
    assumption
    assumption
    assumption
    assumption
    assumption
  contradiction
  
  have d10k : 10 ∣ k-6 := by refine (Nat.modEq_iff_dvd' ?_).mp (id (Eq.symm e6)); linarith
  obtain ⟨d,hd⟩ := d10k
  have : 4 ≤ d := by omega
  have exi : ∃ n, k = 21 + 5 * n := by 
    use (k-21)/5
    have : 5 * ((k - 21) / 5) = k-21 := by 
      refine Nat.mul_div_eq_iff_dvd.mpr ?_;
      have : k - 21 = k - 6 - 15 := by omega
      rw [this]
      rw [hd]
      refine Nat.dvd_sub ?_ ?_ ?_
      omega
      use 2*d
      ring
      use 3
    rw [this]
    omega
  obtain ⟨l,hl⟩ := exi
  let x := 21
  let y := 5*l
  have eq : x + y = k := by omega
  have oddx: Odd x := by use 10; norm_num
  have xge2 : 2 ≤ x := by norm_num
  have nxprime : ¬ Nat.Prime x := by decide
  have oddy: Odd y := by 
    by_contra t
    have eveny : Even y := by exact Nat.not_odd_iff_even.mp t
    have : Odd (x+y) := by exact Even.odd_add eveny oddx
    have : ¬ Even (x+y) := by exact Nat.not_even_iff_odd.mpr this
    rw [eq] at this
    contradiction
  have : 2 ≤ y := by omega
  have nyprime : ¬ Nat.Prime y := by
    by_contra yp
    have d5: 5 ∣ y := by use l
    rw [Nat.dvd_prime] at d5
    obtain t1 | t2 := d5
    simp at t1
    omega
    exact yp
  have : ¬ x+y = k := by 
    apply h
    assumption
    assumption
    assumption
    assumption
    assumption
    assumption
  contradiction

  have d10k : 10 ∣ k-8 := by refine (Nat.modEq_iff_dvd' ?_).mp (id (Eq.symm e8)); linarith
  obtain ⟨d,hd⟩ := d10k
  have : 4 ≤ d := by omega
  have exi : ∃ n, k = 33 + 5 * n := by 
    use (k-33)/5
    have : 5 * ((k - 33) / 5) = k-33 := by 
      refine Nat.mul_div_eq_iff_dvd.mpr ?_;
      have : k - 33 = k - 8 - 25 := by omega
      rw [this]
      rw [hd]
      refine Nat.dvd_sub ?_ ?_ ?_
      omega
      use 2*d
      ring
      use 5
    rw [this]
    omega
  obtain ⟨l,hl⟩ := exi
  let x := 33
  let y := 5*l
  have eq : x + y = k := by omega
  have oddx: Odd x := by use 16; norm_num
  have xge2 : 2 ≤ x := by norm_num
  have nxprime : ¬ Nat.Prime x := by decide
  have oddy: Odd y := by 
    by_contra t
    have eveny : Even y := by exact Nat.not_odd_iff_even.mp t
    have : Odd (x+y) := by exact Even.odd_add eveny oddx
    have : ¬ Even (x+y) := by exact Nat.not_even_iff_odd.mpr this
    rw [eq] at this
    contradiction
  have : 2 ≤ y := by omega
  have nyprime : ¬ Nat.Prime y := by
    by_contra yp
    have d5: 5 ∣ y := by use l
    rw [Nat.dvd_prime] at d5
    obtain t1 | t2 := d5
    simp at t1
    omega
    exact yp
  have : ¬ x+y = k := by 
    apply h
    assumption
    assumption
    assumption
    assumption
    assumption
    assumption
  contradiction