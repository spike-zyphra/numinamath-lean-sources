import Mathlib

theorem number_theory_639821 (Q : ℤ) (p : ℕ) (hp1 : Odd p) (hp2 : Nat.Prime p)
  (a : ℕ → ℤ) (ha0 : a 0 = 0) (ha1 : a 1 = 2)
  (han : ∀ n : ℕ, a (n + 2) = 2 * a (n + 1) + Q * a n)
  (h1 : ∃ x : ℤ, x ^ 2 ≡ 1 + Q [ZMOD p]) (h2 : ¬(1 + Q ≡ 0 [ZMOD p])) (h3 : ¬(Q ≡ 0 [ZMOD p])) :
  (p : ℤ) ∣ a (p - 1) := by 
  obtain ⟨k, hk⟩ := h1
  have prime1 : Fact (Nat.Prime p) := by 
    exact { out := hp2 }
  -- since p is a prime number then ZMod p is a domain.
  have domain1 : IsDomain (ZMod p) := by 
    exact ZMod.instIsDomain p
  have neq1 : ((1 + Q : ℤ) : ZMod p) ≠ (0 : ℤ) := by 
    by_contra hc
    obtain aux1 := (ZMod.intCast_eq_intCast_iff _ _ p).mp hc
    exact h2 aux1
  norm_num at neq1
  have isUnit1 : IsUnit (1 + Q : ZMod p) := by 
    exact Ne.isUnit neq1
  have neq2 : (Q : ZMod p) ≠ (0 : ℤ) := by 
    by_contra hc
    obtain aux1 := (ZMod.intCast_eq_intCast_iff _ _ p).mp hc
    exact h3 aux1
  norm_num at neq2
  have isUnit2 : IsUnit (Q : ZMod p) := by
    exact Ne.isUnit neq2
  have Qeq1 : (k ^ 2 : ℤ) = ((1 + Q : ℤ) : ZMod p) := by 
    exact (ZMod.intCast_eq_intCast_iff' (k ^ 2) (1 + Q) p).mpr hk
  norm_num at Qeq1
  have Qeq2 : (Q : ZMod p) = k ^ 2 - 1 := by 
    rw [Qeq1]
    ring
  have isUnit3 : IsUnit (k : ZMod p) := by
    have keq : (k : ZMod p) ≠  0 := by 
      by_contra hc
      simp [hc] at Qeq1
      exact neq1 (Eq.symm Qeq1)
    exact Ne.isUnit keq

  -- by induction we can prove the following general formula for a n
  have h1 : ∀ n, a n = (k : ZMod p)⁻¹ * ((1 + k) ^ n - (1 - k) ^ n) ∧ 
    a (n + 1) = (k : ZMod p)⁻¹ * ((1 + k) ^ (n + 1) - (1 - k) ^ (n + 1)) := by 
    intro n 
    induction n with 
    | zero => 
      simp [ha0, ha1]
      rw [show (k : ZMod p) + k = k * 2 by ring, ←mul_assoc, ZMod.inv_mul_of_unit _ isUnit3]
      simp
    | succ m ih => 
      obtain ⟨ih1, ih2⟩ := ih
      constructor
      · exact ih2
      rw [han]
      norm_num
      rw [ih1, ih2]
      have aux1 : (1 + k : ZMod p) ^ (m + 1 + 1) = 
        (1 + k) ^ m * (2 + Q + 2 * k) := by 
        rw [show m + 1 + 1 = m + 2 by ring, pow_add]
        rw [Qeq2]
        ring
      have aux2 : (1 - k : ZMod p) ^ (m + 1 + 1) =
        (1 - k) ^ m * (2 + Q - 2 * k) := by
        rw [show m + 1 + 1 = m + 2 by ring, pow_add]
        rw [Qeq2]
        ring
      rw [aux1, aux2, pow_add, pow_add]
      ring
  
  have neq3 : (1 + k : ZMod p) ≠ 0 := by 
    by_contra hc
    have keq : (k : ZMod p) = -1 := by 
      conv => 
        rhs
        rw [←add_zero (-1), ←hc]
      simp
    simp [keq] at Qeq2
    exact neq2 Qeq2
  
  have neq4 : (1 - k : ZMod p) ≠ 0 := by
    by_contra hc
    have keq : (k : ZMod p) = 1 := by 
      conv => 
        lhs
        rw [←add_zero (k : ZMod p), ←hc]
      simp
    simp [keq] at Qeq2
    exact neq2 Qeq2
  -- we prove that a (p - 1) = 0 in ZMod p, then p ∣ a (p - 1)
  have modeq : (a (p - 1) : ZMod p) = 0 := by 
    rw [(h1 (p - 1)).1]
    -- use Fermat little theorem to prove that (1 + k : ZMod p) ^ (p - 1) = 1, using the condition that 1 + k ≠ 0
    have aux1 : (1 + k : ZMod p) ^ (p - 1) = 1 := by 
      refine ZMod.pow_card_sub_one_eq_one neq3
    -- -- use Fermat little theorem to prove that (1 - k : ZMod p) ^ (p - 1) = 1, using the condition that 1 - k ≠ 0
    have aux2 : (1 - k : ZMod p) ^ (p - 1) = 1 := by
      refine ZMod.pow_card_sub_one_eq_one neq4
    rw [aux1, aux2]
    simp
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a (p - 1)) p).mp modeq
  