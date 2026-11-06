import Mathlib

theorem number_theory_627376 : ((2 ^ 859433) - 1) % 10 = 1 := by
  
  have : (2 ^ 859433) % 10 = 2 := by 

    --We prove by induction that 2^x%10 has a period 4.
    --Then, our claim follows by simple calculation.
    have cla : ∀ k:ℕ, 2^(4*k+1) % 10 = 2 ∧ 2^(4*k+2) % 10 = 4 ∧ 2^(4*k+3) % 10 = 8 ∧ 2^(4*k+4) % 10 = 6 := by
      intro k
      induction' k with k hk

      simp

      obtain ⟨hk1,hk2,hk3,hk4⟩ := hk

      have h1: 2 ^ (4 * (k + 1) + 1) % 10 = 2 := by
        have : 4 * (k + 1) + 1 = 4 * k + 4 + 1 := by omega
        rw [this]
        rw [pow_succ]
        rw [Nat.mul_mod]
        rw [hk4]

      have h2: 2 ^ (4 * (k + 1) + 2) % 10 = 4 := by 
        have : 2 ^ (4 * (k + 1) + 2) = 2 ^ (4 * (k + 1) + 1 + 1) := by ring
        rw [this]
        rw [pow_succ]
        rw [Nat.mul_mod]
        rw [h1]
      have h3: 2 ^ (4 * (k + 1) + 3) % 10 = 8 := by
        have : 2 ^ (4 * (k + 1) + 3) = 2 ^ (4 * (k + 1) + 2 + 1) := by ring
        rw [this]
        rw [pow_succ]
        rw [Nat.mul_mod]
        rw [h2]        
      have h4: 2 ^ (4 * (k + 1) + 4) % 10 = 6 := by 
        have : 2 ^ (4 * (k + 1) + 4) = 2 ^ (4 * (k + 1) + 1 + 3) := by ring
        rw [this]
        rw [pow_succ]
        rw [Nat.mul_mod]
        rw [h3]

      tauto

    specialize cla 214858
    have : 859433 = 4*214858 +1 := by ring_nf
    rw [←this] at cla
    exact cla.left

  omega