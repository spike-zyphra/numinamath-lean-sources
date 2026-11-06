import Mathlib

/-
5. The first four members of a sequence are: $2,0,1,8$. Each subsequent member of the sequence is the unit digit of the sum of the previous four members. (e.g., the fifth member is 1). Is the 2018th member of the sequence an even or odd number? Justify your answer!
-/








--We first show that the parity of m % 10 is the same as the parity of m, for every natural number m.
lemma l1 (m:ℕ):
Even (m % 10) ↔ Even (m) := by
  
  have cla : 10 * (m / 10) + m % 10 = m := by exact Nat.div_add_mod m 10
  have e1 : Even (10 * (m / 10)) := by use 5 * (m/10); omega
  
  constructor
  
  intro h
  rw [← cla]
  exact Even.add e1 h

  intro h
  refine Even.mod_even h ?_
  use 5

lemma l2 (m:ℕ):
Odd (m % 10) ↔ Odd (m) := by
  constructor
  
  intro h
  by_contra hh
  have : Even m := by exact Nat.not_odd_iff_even.mp hh
  have : Even (m%10) := by rw [l1]; exact this
  have :¬ Odd (m%10) := by exact Nat.not_odd_iff_even.mpr this
  contradiction

  intro h
  by_contra hh
  have : Even (m%10) := by exact Nat.not_odd_iff_even.mp hh
  have : Even (m) := by rw [←l1]; exact this
  have :¬ Odd (m) := by exact Nat.not_odd_iff_even.mpr this
  contradiction


theorem number_theory_243387 (a : ℕ → ℕ) (h1 : a 1 = 2) (h2 : a 2 = 0) (h3 : a 3 = 1) (h4 : a 4 = 8) (h: ∀n≥5, a n = (a (n-4) + a (n-3) + a (n-2) + a (n-1))%10):
    Odd (a 2018) := by
  
  have h5 : a 5 = 1 := by 
    simp [h, h1, h2, h3, h4]

  --We prove that the parity of a has a period 5 by induction.
  have cla : ∀k:ℕ, Even (a (5*k+1)) ∧ Even (a (5*k+2)) ∧ Odd (a (5*k+3)) ∧ Even (a (5*k+4)) ∧ Odd (a (5*k+5)) := by 
    intro k
    induction' k with k hk

    simp [h, h1, h2, h3, h4, h5]
    use 4

    obtain ⟨h1,h2,h3,h4,h5⟩ := hk
    ring_nf at h1 h2 h3 h4 h5
    have : 2+k*5 = 5 + k * 5 - 3 := by omega
    rw [this] at h2
    have : 3+k*5 = 5 + k * 5 - 2 := by omega
    rw [this] at h3
    have : 4+k*5 = 5 + k * 5 - 1 := by omega
    rw [this] at h4
    have : 5+k*5 = 5 + k * 5  := by omega
    rw [this] at h5

    have h6 : Even (a (5 * (k + 1) + 1))  := by 
      specialize h (5*(k+1)+1) (by linarith)
      simp [h]
      rw [l1]
      ring_nf
      apply Odd.add_odd
      apply Odd.add_even
      exact Even.add_odd h2 h3
      exact h4
      exact h5

    ring_nf at h6

    have h7 : Even (a (5 * (k + 1) + 2))  := by 
      specialize h (5*(k+1)+2) (by linarith)
      simp [h]
      rw [l1]
      ring_nf
      apply Even.add
      apply Odd.add_odd
      exact Even.odd_add h4 h3
      exact h5
      exact h6
    ring_nf at h7

    have h8 : Odd  (a (5 * (k + 1) + 3))  := by 
      specialize h (5*(k+1)+3) (by linarith)
      simp [h]
      rw [l2]
      ring_nf
      apply Odd.add_even
      apply Odd.add_even
      exact Even.add_odd h4 h5
      exact h6
      exact h7
    ring_nf at h8

    have h9 : Even (a (5 * (k + 1) + 4))  := by 
      specialize h (5*(k+1)+4) (by linarith)
      simp [h]
      rw [l1]
      ring_nf
      apply Odd.add_odd
      apply Odd.add_even
      exact Even.odd_add h6 h5
      exact h7
      exact h8
    ring_nf at h9

    have h10: Odd  (a (5 * (k + 1) + 5))  := by 
      specialize h (5*(k+1)+5) (by linarith)
      simp [h]
      rw [l2]
      ring_nf
      apply Odd.add_even
      apply Even.add_odd
      exact Even.add h6 h7
      exact h8
      exact h9
    ring_nf at h10

    ring_nf; tauto

  --Now, the parity of a 2018 is the same as the parity of a 3, so it is odd.
  specialize cla 403
  simp at cla
  tauto
