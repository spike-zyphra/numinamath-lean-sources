import Mathlib

theorem number_theory_637673 (K : ℕ) (M : ℕ) (c : ℕ) (a : ℕ) (g : ZMod M)
  (hg : IsPrimitiveRoot g (M - 1))
  (hK : K > 0) (hM : Nat.Prime M) (hc : c ≥ 1) (hM1 : M = c * K + 1)
  (ha : a = g ^ c) (h1 : 1 ≤ a) (h2 : a ≤ 2019) :
  IsLeast {T : ℕ | 0 < T ∧ a ^ T ≡ 1 [ZMOD M]} K := by 
  unfold IsLeast
  constructor
  · simp
    constructor
    · exact hK
    · 
      have modeq1 : (a : ZMod M) ^ K = 1 := by 
        rw [ha, ←pow_mul]
        have eq1 : c * K = M - 1 := by 
          rw [hM1]
          omega
        rw [eq1]
        have prime1 : Fact (Nat.Prime M) := by 
          exact { out := hM }
        apply ZMod.pow_card_sub_one_eq_one
        by_contra hc1
        have pos : M - 1 > 0 := by 
          have mge2 : M ≥ 2 := by 
            exact Nat.Prime.two_le hM
          omega
        obtain ⟨hg1, hg2⟩ := (IsPrimitiveRoot.iff pos).mp hg 
        rw [hc1] at hg1
        have eq0 : (0 : ZMod M) ^ (M - 1) = 0 := by 
          exact Mathlib.Tactic.Ring.zero_pow pos
        rw [eq0] at hg1
        have neq : 0 ≠ (1 : ZMod M) := by
          exact (zero_ne_one' (ZMod M))
        exact neq hg1
      refine (ZMod.intCast_eq_intCast_iff _ _ _ ).mp ?_
      norm_cast
      norm_cast at modeq1
    
  · unfold lowerBounds
    simp
    intro n hn hnmod
    have modeq1 : (a : ZMod M) ^ n = 1:= by 
      obtain aux := (ZMod.intCast_eq_intCast_iff _ _ _ ).mpr hnmod
      norm_cast at aux
      norm_cast
    rw [ha, ←pow_mul] at modeq1
    obtain h3 := (IsPrimitiveRoot.pow_eq_one_iff_dvd hg (c * n)).mp modeq1
    have ge1 : c * n ≥ M - 1 := by 
      apply Nat.le_of_dvd
      positivity
      exact h3
    rw [hM1, show c * K + 1 - 1 = c * K by omega] at ge1
    nlinarith
  