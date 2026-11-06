import Mathlib

/-
Let $k$ be a positive integer. Determine the units digit of the product $16^k \times 17^{k+1} \times 18^{k+2}$. Show that the answer is 8.
-/


--The lemma about the unit digits of 16^k.
lemma l16 (k:ℕ) (kpos: 0 < k):
  16^k % 10 = 6 := by 
  
  induction' k with k hk

  simp at kpos

  by_cases ke0 : k = 0
  simp [ke0]
  have kpos: 0 < k := by omega
  simp [kpos] at hk
  rw [Nat.pow_succ]
  rw [Nat.mul_mod]
  rw [hk]


--The lemma about the unit digits of 17^k.
lemma l17 (k:ℕ) :
  17^(4*k + 1) % 10 = 7 ∧
  17^(4*k + 2) % 10 = 9 ∧
  17^(4*k + 3) % 10 = 3 ∧ 
  17^(4*k + 4) % 10 = 1
  := by
  
  induction' k with k hk

  simp

  obtain ⟨h1,h2,h3,h4⟩ := hk

  have h5 : 17 ^ (4 * (k + 1) + 1) % 10 = 7  := by 
    rw [pow_succ]
    have : 4 * (k+1) = 4*k+4 := by ring
    rw [this]
    rw [Nat.mul_mod]
    simp [h4]

  have h6 : 17 ^ (4 * (k + 1) + 2) % 10 = 9  := by 
    rw [pow_succ]
    rw [Nat.mul_mod]
    simp [h5]

  have h7 : 17 ^ (4 * (k + 1) + 3) % 10 = 3  := by 
    rw [pow_succ]
    rw [Nat.mul_mod]
    simp [h6]

  have h8 : 17 ^ (4 * (k + 1) + 4) % 10 = 1  := by
    rw [pow_succ]
    rw [Nat.mul_mod]
    simp [h7]
  
  tauto


--The lemma about the unit digits of 18^k.
lemma l18 (k:ℕ) :
  18^(4*k + 1) % 10 = 8 ∧
  18^(4*k + 2) % 10 = 4 ∧
  18^(4*k + 3) % 10 = 2 ∧ 
  18^(4*k + 4) % 10 = 6
  := by
  
  induction' k with k hk

  simp

  obtain ⟨h1,h2,h3,h4⟩ := hk

  have h5 : 18 ^ (4 * (k + 1) + 1) % 10 = 8  := by 
    rw [pow_succ]
    have : 4 * (k+1) = 4*k+4 := by ring
    rw [this]
    rw [Nat.mul_mod]
    simp [h4]

  have h6 : 18 ^ (4 * (k + 1) + 2) % 10 = 4  := by 
    rw [pow_succ]
    rw [Nat.mul_mod]
    simp [h5]

  have h7 : 18 ^ (4 * (k + 1) + 3) % 10 = 2  := by 
    rw [pow_succ]
    rw [Nat.mul_mod]
    simp [h6]

  have h8 : 18 ^ (4 * (k + 1) + 4) % 10 = 6  := by
    rw [pow_succ]
    rw [Nat.mul_mod]
    simp [h7]
  
  tauto

theorem number_theory_642103 (k : ℕ) (kpos: 0 < k):
  (16^k * 17^(k+1) * 18^(k+2)) % 10 = 8  := by

  rw [Nat.mul_mod]
  nth_rw 2 [Nat.mul_mod]

  --Now we apply the three lemmas we got. We consider the value of k % 4 and divide the remaining proof into 4 parts.
  have t16 : 16 ^ k % 10 = 6 := l16 k kpos

  by_cases km41 : k % 4 = 1
  have : 4 ∣ k - 1 := by exact (Nat.modEq_iff_dvd' kpos).mp (id (Eq.symm km41))
  obtain ⟨d,hd⟩ := this
  have ke1 : k+1 = 4*d + 2 := by omega
  have ke2 : k+2 = 4*d + 3 := by omega
  have t17 : 17 ^ (4*d+2) % 10 = 9 := (l17 d).right.left
  have t18 : 18 ^ (4*d+3) % 10 = 2 := (l18 d).right.right.left
  rw [←ke1] at t17
  rw [←ke2] at t18
  simp [t16,t17,t18]

  by_cases km42 : k % 4 = 2 
  have : 4 ∣ k - 2 := by refine (Nat.modEq_iff_dvd' ?_).mp (id (Eq.symm km42)); omega
  obtain ⟨d,hd⟩ := this
  have ke1 : k+1 = 4*d + 3 := by omega
  have ke2 : k+2 = 4*d + 4 := by omega
  have t17 : 17 ^ (4*d+3) % 10 = 3 := (l17 d).right.right.left
  have t18 : 18 ^ (4*d+4) % 10 = 6 := (l18 d).right.right.right
  rw [←ke1] at t17
  rw [←ke2] at t18
  simp [t16,t17,t18]

  by_cases km43 : k % 4 = 3 
  have : 4 ∣ k - 3 := by refine (Nat.modEq_iff_dvd' ?_).mp (id (Eq.symm km43)); omega
  obtain ⟨d,hd⟩ := this
  have ke1 : k+1 = 4*d + 4 := by omega
  have ke2 : k+2 = 4*(d+1) + 1 := by omega
  have t17 : 17 ^ (4*d+4) % 10 = 1 := (l17 d).right.right.right
  have t18 : 18 ^ (4*(d+1)+1) % 10 = 8 := (l18 (d+1)).left
  rw [←ke1] at t17
  rw [←ke2] at t18
  simp [t16,t17,t18]

  have km40 : k % 4 = 0 := by omega
  have : 4 ∣ k := by exact Nat.dvd_of_mod_eq_zero km40
  obtain ⟨d,hd⟩ := this
  have ke1 : k+1 = 4*d + 1 := by omega
  have ke2 : k+2 = 4*d + 2 := by omega
  have t17 : 17 ^ (4*d+1) % 10 = 7 := (l17 d).left
  have t18 : 18 ^ (4*d+2) % 10 = 4 := (l18 d).right.left
  rw [←ke1] at t17
  rw [←ke2] at t18
  simp [t16,t17,t18]
