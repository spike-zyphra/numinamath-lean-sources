import Mathlib

/-Let the two-digit numbers ${ }^{\overline{a b}}$ and ${ }^{\overline{c d}}$ be such that the ratio of the four-digit number $\overline{a b c d}$
to the sum $\overline{a b}+\overline{c d}$ is an integer. Find all possible values that this number can take.-/
theorem number_theory_250137 : {k | ∃ (a b c d : ℕ),(1 ≤ a ∧ a ≤ 9)∧(0 ≤ b ∧ b ≤ 9)
  ∧(1 ≤ c ∧ c ≤ 9)∧(0 ≤ d ∧ d ≤ 9)∧(1000 * a + 100 * b + 10 * c + d = k * (10 * a + b + 10 * c + d))} =
    Finset.Icc 11 90 := by
  apply Set.ext
  intro k
  constructor
  intro hk
  rcases hk with ⟨a,b,c,d,ha,hb,hc,hd,h⟩ 
  have h1 : k ≤ 90 := by
    by_cases h2 : k ≤ 90
    · linarith
    · -- Now we prove k ≤ 90 by contradiction. Assume k ≥ 91, we'll derive a contradiction.
      push_neg at h2
      have h2' : k ≥ 91 := by linarith
      have h3 : 10 ≤ a * 10 + b := by
        omega
      have h4 : a * 10 + b ≤ 99 := by
        omega
      have h5 : 10 ≤ c * 10 + d := by
        omega
      have h6 : c * 10 + d ≤ 99 := by
        omega
      nlinarith [h2', h3, h4, h5, h6, h]
    
  have h7 : 11 ≤ k := by
    by_cases h8 : k ≥ 11
    · linarith
    · -- Now we prove k ≥ 11 by contradiction. Assume k ≤ 10, we'll derive a contradiction.
      push_neg at h8
      have h8' : k ≤ 10 := by linarith
      have h9 : 10 ≤ a * 10 + b := by
        omega
      have h10 : a * 10 + b ≤ 99 := by
        omega
      have h11 : 10 ≤ c * 10 + d := by
        omega
      have h12 : c * 10 + d ≤ 99 := by
        omega
      nlinarith [h8', h9, h10, h11, h12, h]
  
  exact Finset.mem_Icc.mpr ⟨h7, h1⟩

  intro hk
  simp at hk
  rcases hk with ⟨hk1, hk2⟩
  -- For 11 ≤ k ≤ 90, we prove it's achievable by giving specific values for a, b, c, d.
  use (k-1)/10,(k-1)%10,(100-k)/10,(100-k)%10
  constructor;omega;constructor;omega;constructor;omega;constructor;omega
  have h13 : 10 * ((100 - k )/ 10)+((100 - k) % 10)= 100 - k:= by omega
  have h14:10*((k-1) / 10)+((k-1) % 10) = k-1 := by omega
  have h15 : 1000 * ((k - 1) / 10) + 100 * ((k - 1) % 10) = 100 * (k-1) := by
    nth_rewrite 3 [← h14] ;omega
  rw[h14,add_assoc,add_assoc (k-1),h13,h15]
  have h16 : k - 1 + (100 - k) = 99 := by omega
  have h17 : 100 * (k - 1) + (100 - k) = 99 * k := by omega
  rw [h16,h17,mul_comm]

  

