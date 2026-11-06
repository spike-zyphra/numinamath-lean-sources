import Mathlib

theorem number_theory_57173 :
    IsGreatest {n : ℕ | n ∈ Finset.Icc 10 99 ∧ 4 ∣ n ∧ 
                        ∀m > 0, n^m ≡ n [MOD 100]} 76 := by
  constructor
  · -- Show 76 is in the set
    constructor
    · -- Show 76 in Finset.Icc 10 99
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show 4 divides 76
      norm_num
    · -- Show that ∀m > 0, 76^m ≡ 76 [MOD 100]
      intro m hm
      have h1 : ∀ m > 0, (76 : ℕ) ^ m % 100 = 76 := by
        intro m hm
        induction m with
        | zero =>
          linarith
        | succ m ih =>
          cases m with
          | zero => 
            simp
          | succ m => 
            simp [Nat.pow_succ, Nat.mul_mod] at ih ⊢
            omega
      have h3 := h1 m hm
      simp [Nat.ModEq, Nat.pow_mod, h3]
  · -- Show there's no greater element in the set
    intro n hn
    rcases hn with ⟨hn1, hn2, hn3⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn4, hn5⟩
    by_contra h 
    push_neg at h 
    have h1 := hn3 2 (by norm_num)
    have h1' := h1
    simp [Nat.ModEq] at h1' ⊢
    have h2 : n % 4 = 0 := by 
      exact Nat.dvd_iff_mod_eq_zero.mp hn2
    interval_cases n <;> norm_num at h1' h2 hn4 hn5 <;> omega