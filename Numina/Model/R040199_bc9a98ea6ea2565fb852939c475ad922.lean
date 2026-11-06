import Mathlib

theorem number_theory_295886 (n : ℕ) (hn : n > 0) :
    7 ∣ 3^n + n^3 ↔ 7 ∣ 3^n * n^3 + 1 := by 
  have p7 : Nat.Prime 7 := by norm_num
  haveI : Fact (Nat.Prime 7) := ⟨p7⟩

  obtain h7n | h7n := @or_not (7 ∣ n)
  
  . have h₁ : 7 ∣ n^3 := by calc 
      7 ∣ n := h7n
      _ ∣ n^3 := by exact Dvd.intro_left (n.pow 2) rfl
    have h₂ : 7 ∣ 3^n * n^3 := by exact Dvd.dvd.mul_left h₁ _
    
    rw [← Nat.dvd_add_iff_left h₁, ← Nat.dvd_add_iff_right h₂]
    simp
    by_contra h
    
    have : 7 ∣ 3 := Nat.Prime.dvd_of_dvd_pow p7 h
    norm_num at this

  . repeat rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
    have hn_pow : (n:ZMod 7)^(7-1) = 1 := by
      refine ZMod.pow_card_sub_one_eq_one ?_
      by_contra h
      have := by exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp h
      contradiction
    
    simp at hn_pow
    push_cast
    constructor <;> rintro h
    . have : ((3: ZMod 7)^n + (n: ZMod 7)^3) * (n: ZMod 7)^3 = 0 := by rw [h]; simp
      ring_nf at this
      rw [hn_pow] at this
      ring_nf at *
      exact this
    . have : ((3: ZMod 7)^n * (n: ZMod 7)^3 + 1) * (n: ZMod 7)^3 = 0 := by rw [h]; simp
      ring_nf at this
      rw [hn_pow] at this
      ring_nf at *
      exact this