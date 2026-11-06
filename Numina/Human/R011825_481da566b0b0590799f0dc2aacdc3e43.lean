import Mathlib

/-
Exercise 12. Determine all triplets of positive integers $(\mathrm{a}, \mathrm{b}, \mathrm{n})$ satisfying:

$$
a!+b!=2^{n}
$$
-/

theorem number_theory_293643 (a b n : ℕ) (ha : 0 < a) (hb : 0 < b) (hn : 0 < n):
Nat.factorial a + Nat.factorial b = 2 ^ n ↔ (a, b, n) ∈ ({(1, 1, 1), (2, 2, 2), (2, 3, 3), (3,2,3)} : Set <| ℕ × ℕ × ℕ) := by
  simp
  constructor

  --From left to right
  intro h

  --Wlog a ≤ b
  wlog aleb : a ≤ b
  have : b = 1 ∧ a = 1 ∧ n = 1 ∨ b = 2 ∧ a = 2 ∧ n = 2 ∨ b = 2 ∧ a = 3 ∧ n = 3 ∨ b = 3 ∧ a = 2 ∧ n = 3 := by
    apply this b a n
    repeat assumption
    linarith
    omega
  tauto

  --We first prove that b ≤ 3.
  --If 3<b, then 3 ∣ b! but ¬ 3 ∣ 2^n, so a ≤ 2. But either a = 1 or a = 2 leads to a contradiction.
  have ble3 : b ≤ 3 := by 
    by_contra nble3
    have bge4 : 4 ≤ b := by omega
    have d4bf : 4 ∣ b.factorial := by refine Nat.dvd_factorial ?_ bge4; norm_num
    have d42n : 4 ∣ 2^n := by 
      have nge2 : 2 ≤ n := by 
        have t1: (4).factorial ≤ b.factorial := by exact Nat.factorial_le bge4
        have : (4).factorial = 24 := by decide
        rw [this] at t1
        have : 0 ≤ a.factorial := by positivity
        have : 24 ≤ 2^n := by linarith

        by_contra nn
        have : n ≤ 1 := by omega
        have : 2^n ≤ 2^1 := by refine Nat.pow_le_pow_of_le ?_ this; linarith
        linarith
      use 2^(n - 2)
      have : 4 = 2^2 := by omega
      rw [this]
      rw [← pow_add]
      have : 2+(n-2)= n := by omega
      rw[this]
    have d4af : 4 ∣ a.factorial := by
      rw [← h] at d42n
      rw [Nat.dvd_add_left] at d42n
      exact d42n
      exact d4bf

    have d3fb: 3 ∣ b.factorial := by refine Nat.dvd_factorial ?_ ?_; norm_num; linarith
    have ale2 : a ≤ 2 := by
      by_contra nale2
      have age3 : 3 ≤ a := by omega
      have d3fa: 3 ∣ a.factorial := by refine Nat.dvd_factorial ?_ age3; norm_num
      have : 3 ∣ a.factorial + b.factorial := by exact (Nat.dvd_add_iff_right d3fa).mp d3fb
      rw [h] at this
      have p2 : Nat.Prime 2 := by exact Nat.prime_two
      have p3 : Nat.Prime 3 := by exact Nat.prime_three
      have : 3 ∣ 2 := by exact Nat.Prime.dvd_of_dvd_pow p3 this
      have : 3 ≤ 2 := by exact (Nat.Prime.dvd_factorial p3).mp this
      linarith
    by_cases ae1 : a = 1
    rw [ae1] at d4af
    simp at d4af

    have ae2 : a = 2 := by omega
    simp [ae2] at d4af
    have : 4 ≤ 2 := by apply Nat.le_of_dvd; norm_num; exact d4af
    linarith

  --Now we just enumerate the possible cases b = 1 2 or 3.
  by_cases be1 : b = 1
  have ae1 : a = 1 := by omega
  simp [ae1,be1] at h
  have ne1 : n = 1 := by 
    symm at h
    rw [Nat.pow_eq_self_iff] at h
    exact h
    omega
  tauto

  by_cases be2 : b = 2
  
  by_cases ae1 : a = 1
  simp [ae1,be2] at h
  have : Even 3 := by 
    use 2^(n-1)
    rw [←mul_two]
    rw [←pow_succ]
    have : n-1+1 = n := by omega
    rw [this]
    exact h
  exfalso;
  have : Odd 3 := by use 1; simp
  have : ¬ Even 3 := by exact Nat.not_even_iff.mpr rfl
  contradiction

  have ae2 : a = 2 := by omega
  simp [ae2,be2] at h
  have ne2 : n = 2 := by
    symm at h
    have : 4 = 2^2 := by norm_num
    rw [this] at h
    rw [pow_right_inj₀] at h
    exact h
    omega
    omega
  tauto
  
  have f3: Nat.factorial 3 = 6 := by decide
  have be3 : b = 3 := by omega
  by_cases ae1 : a = 1
  simp [ae1,be3,f3] at h
  exfalso
  have : 7 ∣ 2^n := by rw [← h];
  have p2 : Nat.Prime 2 := by exact Nat.prime_two
  have p7 : Nat.Prime 7 := by norm_num
  have : 7 ∣ 2 := by exact Nat.Prime.dvd_of_dvd_pow p7 this
  have : 7 ≤ 2 := by exact (Nat.Prime.dvd_factorial p7).mp this
  linarith
  by_cases ae2 : a = 2
  simp [ae2,be3,f3] at h
  have : 8 = 2^3 := by norm_num
  rw [this] at h
  rw [pow_right_inj₀] at h
  symm at h
  tauto
  omega
  norm_num
  have ae3 : a = 3 := by omega
  rw [ae3,be3] at h
  rw [f3] at h
  simp at h
  exfalso
  have : 3 ∣ 2^n := by rw [← h]; use 4
  have p2 : Nat.Prime 2 := by exact Nat.prime_two
  have p3 : Nat.Prime 3 := by exact Nat.prime_three
  have : 3 ∣ 2 := by exact Nat.Prime.dvd_of_dvd_pow p3 this
  have : 3 ≤ 2 := by exact (Nat.Prime.dvd_factorial p3).mp this
  linarith

  --From right to left, simple calculation to show that all values are valid.
  intro h
  rcases h with ⟨ae,be,ne⟩ | ⟨ae,be,ne⟩ | ⟨ae,be,ne⟩ | ⟨ae,be,ne⟩ <;>
  simp [ae,be,ne] <;> decide