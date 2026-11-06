import Mathlib

theorem number_theory_106731 {n : ℕ} (hn : Odd n) (S1 S2 : ℤ)
    (hS1 : S1 = ∑ i in Finset.range n, (i + 1)) (hS2 : S2 = ∑ i in Finset.range n, (-1 : ℤ)^i * (i + 1))
    (hS1' : S1 = 2015 * S2) :
    n = 2015 := by 
  have h1 : n % 2 = 1 := by 
    obtain ⟨k, hk⟩ := hn 
    omega 
  have hS1n : S1 = (n : ℤ) * ((n : ℤ) + 1) / 2 := by 
    rw [hS1]
    have h2 : ∀ n : ℕ, ∑ i in Finset.range n, (i + 1 : ℤ) = (n : ℤ) * ((n : ℤ) + 1) / 2 := by 
      intro n 
      induction n with 
      | zero => 
        simp 
      | succ n ih => 
        rw [Finset.sum_range_succ, ih] 
        cases n with 
        | zero => 
          all_goals simp 
        | succ n => 
          simp [add_assoc, mul_add] at *
          <;> ring_nf <;> omega 
    specialize h2 n 
    simpa using h2 
  have hS2n : S2 = (n + 1 : ℤ) / 2 := by 
    rw [hS2]
    have h5 : ∀ n : ℕ, Odd n → ∑ i in Finset.range n, (-1 : ℤ) ^ i * (i + 1) = (n + 1 : ℤ) / 2 := by 
      intro n hn 
      obtain ⟨k, hk⟩ := hn 
      rw [show n = 2 * k + 1 by linarith [hk]]
      have h6 : ∀ k : ℕ, ∑ i in Finset.range (2 * k + 1), (-1 : ℤ) ^ i * (i + 1 : ℤ) = (k + 1 : ℤ) := by 
        intro k 
        induction k with 
        | zero => 
          norm_num 
        | succ k ih => 
          rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring]
          rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
          simp [pow_two, pow_zero, pow_succ] at *
          <;> ring_nf 
          <;> omega 
      specialize h6 k 
      have h7 : (2 * k + 1 + 1 : ℤ) / 2 = (k + 1 : ℤ) := by 
        omega 
      omega 
    specialize h5 n hn 
    assumption 
  rw [hS1n] at hS1' 
  rw [hS2n] at hS1' 
  have eq1 : (n : ℤ) * ((n : ℤ) + 1) = 2015 * ((n + 1 : ℤ)) := by 
    have eq2 : (n : ℤ) * ((n : ℤ) + 1) / 2 = 2015 * ((n + 1 : ℤ) / 2) := by 
      exact_mod_cast hS1' 
    have h43 : ((n + 1 : ℤ) ) % 2 = 0 := by 
      have : n % 2 = 1 := h1 
      have hn1 : (n : ℤ) % 2 = 1 := by 
        omega 
      omega 
    have h46 : (n : ℤ) * ((n : ℤ) + 1) % 2 = 0 := by 
      have : (n : ℤ) % 2 = 1 := by 
        omega 
      have h47 : ((n + 1 : ℤ) ) % 2 = 0 := by 
        omega 
      simp [Int.add_emod, Int.mul_emod, Int.sub_emod, this, h47] 
    omega 
  have h20 : (n + 1 : ℤ) ≠ 0 := by 
    by_contra h 
    have h5 : (n : ℤ) = -1 := by 
      omega 
    have hn2 : n = 0 := by 
      omega 
    have : n % 2 = 0 := by 
      omega 
    omega 
  have eq1' : (n : ℤ) * ((n + 1 : ℤ)) = 2015 * ((n + 1 : ℤ)) := eq1 
  have h8 : (n : ℤ) = (2015 : ℤ) := by 
    apply (mul_right_inj' (show (n + 1 : ℤ) ≠ 0 by assumption)).mp 
    linarith 
  have h21 : n = 2015 := by 
    omega 
  assumption