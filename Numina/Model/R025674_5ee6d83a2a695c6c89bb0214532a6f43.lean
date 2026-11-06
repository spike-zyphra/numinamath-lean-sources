import Mathlib

open Finset Real Nat

theorem inequalities_129200 {n : ℕ} (hn : 0 < n) (a : ℕ → ℕ)
    (ha : ∀ i ∈ Icc 1 n, 0 < a i) :
    ∏ i ∈ Icc 1 n, (a i)! < ((∑ i ∈ Icc 1 n, a i) + 1)! := by 
  have h1 : ∀ i ∈ Icc 1 n, a i ≥ 1 := by 
    intro i hi
    have h2 : 0 < a i := ha i hi
    omega
  have h2 : ∀ k : ℕ, 
      (∏ i ∈ Icc 1 k, (a i)!) ≤ (∑ i ∈ Icc 1 k, a i)! := by
    intro k
    induction k with 
    | zero => 
      simp 
    | succ k ih => 
      rw [prod_Icc_succ_top (by linarith), sum_Icc_succ_top (by linarith)]
      have h6 : ((∑ i in Icc 1 k, a i) + a (k + 1))! ≥ (∏ i in Icc 1 k, (a i)!) * (a (k + 1))! := by 
        have h7 : ( (∑ i in Icc 1 k, a i) )! * (a (k + 1))! ∣ ( (∑ i in Icc 1 k, a i) + a (k + 1) )! := by 
          apply Nat.factorial_mul_factorial_dvd_factorial_add
        have h8 : ( (∑ i in Icc 1 k, a i) + a (k + 1) )! ≥ ( ( (∑ i in Icc 1 k, a i) )! * (a (k + 1))! ) := by 
          exact Nat.le_of_dvd (by positivity) h7 
        have h9 : (∏ i in Icc 1 k, (a i)!) ≤ ( (∑ i in Icc 1 k, a i) )! := by 
          linarith [ih] 
        have h10 : (∏ i in Icc 1 k, (a i)!) * (a (k + 1))! ≤ ( ( (∑ i in Icc 1 k, a i) )! * (a (k + 1))! ) := by 
          nlinarith [h9, show (a (k + 1))! > 0 by positivity] 
        linarith [h10, h8] 
      nlinarith [show (a (k + 1))! > 0 by positivity, show (∑ i in Icc 1 k, a i) ≥ 0 by positivity] 
  have h13 : (∏ i ∈ Icc 1 n, (a i)!) ≤ (∑ i ∈ Icc 1 n, a i)! := by 
    specialize h2 n
    simpa using h2 
  have h14 : (∑ i ∈ Icc 1 n, a i)! < ((∑ i ∈ Icc 1 n, a i) + 1)! := by 
    have h15 : ((∑ i ∈ Icc 1 n, a i) + 1)! = 
      ((∑ i ∈ Icc 1 n, a i) + 1) * ((∑ i ∈ Icc 1 n, a i))! := by 
      simp [Nat.factorial]
      <;> ring 
    rw [h15] at *
    have h16 : (∑ i ∈ Icc 1 n, a i) ≥ 1 := by
      have h17 : n ≥ 1 := by linarith 
      have h18 : ∑ i in Icc 1 n, a i ≥ ∑ i in Icc 1 n, 1 := by
        apply Finset.sum_le_sum 
        intro i hi 
        have h19 : a i ≥ 1 := h1 i hi 
        linarith 
      have h20 : ∑ i in Icc 1 n, (1 : ℕ) = n := by 
        simp 
      have h21 : ∑ i in Icc 1 n, a i ≥ n := by 
        linarith [h18, h20]
      omega 
    have h17 : ((∑ i ∈ Icc 1 n, a i) + 1) > 1 := by 
      omega 
    have h18 : ((∑ i ∈ Icc 1 n, a i))! > 0 := by 
      apply Nat.factorial_pos 
    nlinarith [show 0 < ((∑ i ∈ Icc 1 n, a i) + 1) * ((∑ i ∈ Icc 1 n, a i))! from by nlinarith [Nat.factorial_pos (∑ i ∈ Icc 1 n, a i), h17]]
  linarith [h13, h14]