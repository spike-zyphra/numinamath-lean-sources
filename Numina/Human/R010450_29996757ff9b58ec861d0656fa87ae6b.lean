import Mathlib 

/-
Let $p=2^{24036583}-1$, the largest prime currently known. For how many positive integers $c$ do the quadratics $\pm x^{2} \pm p x \pm c$ all have rational roots?
-/
theorem  number_theory_611386 (p: ℕ) (hp: p = 2^24036583-1)
  -- this is a workaround to deal with the large exponent
  (hprime: Nat.Prime p):  
  -- This is equivalent to both discriminants $p^{2} \\pm 4 c$ being squares.
  let rational_root (c:ℕ+) := (∃ a b: ℤ, a*a = p*p - 4*c ∧ b*b= p*p + 4*c);
  ∀ c: ℕ+, ¬ rational_root c
  := by
    haveI _: Fact (Nat.Prime p) := ⟨hprime⟩
    
    intro rational_root
    simp_rw [rational_root]
    
    have hpmod3 : p ≡ 3 [MOD 4] := by 
      rw[hp]
      native_decide

    push_neg
    intro c a b h
    by_contra h'
    
    have hpmod3': ¬p ≡ 3 [MOD 4] := by
      -- $p^{2}$ must be the average of two squares $a^{2}$ and $b^{2}$. 
      -- Note that $a$ and $b$ must have the same parity, and that $\\left(\\frac{a+b}{2}\\right)^{2}+\\left(\\frac{a-b}{2}\\right)^{2}=\\frac{a^{2}+b^{2}}{2}=p^{2}$.
      have h₀: (a^2+b^2) = 2*p^2 := by rw[pow_two, pow_two, h, h']; ring_nf; 
      have h₁: (a^2:ZMod p) = -b^2 := by 
        rwa [
          show a ^ 2 + b ^ 2 = 2 * ↑p ^ 2 ↔ (a ^ 2 + b ^ 2)%p = (2 * ↑p ^ 2)%p by simp only [iff_true_right, HMod.hMod, h₀],
          show  2 * (p:ℤ) ^ 2 % (p:ℤ) = 0 by rw[pow_two, ←mul_assoc, Int.mul_emod_left],
          show (a ^ 2 + b ^ 2) % ↑p = 0 ↔  a ^ 2 + b ^ 2 ≡ 0 [ZMOD p] by exact Eq.to_iff rfl,
          show a ^ 2 + b ^ 2 ≡ 0 [ZMOD p] ↔ a ^ 2 ≡  -b ^ 2 [ZMOD p] by simp_rw [Int.ModEq, Int.emod_eq_emod_iff_emod_sub_eq_zero]; ring_nf,
          show a ^ 2 ≡ -b ^ 2 [ZMOD p] ↔  (a^2:ZMod p) = (-b^2 : ZMod p) by simp_rw [←ZMod.intCast_eq_intCast_iff]; norm_cast
        ] at h₀

      have h₂ : ¬ a ≡ 0 [ZMOD p] := by 
        by_contra ha
        rw [Int.modEq_comm , Int.modEq_iff_dvd, dvd_iff_exists_eq_mul_right, sub_zero] at ha
        obtain ⟨k,hk⟩ := ha

        have h₃: k = 0 := by
          replace h : 4*c = p^2*(1 - k^2) := by rw [hk] at h; linarith [h]
          replace h := calc  p^2*(1 - k^2) = 4*c := h.symm
            _ > 0                           := by simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, Nat.cast_pos, PNat.pos]
          replace h : 1 - k^2 > 0 := by nlinarith [h]
          replace h : k = 0 := by nlinarith [h]
          exact h

        simp_rw [h₃, mul_zero] at hk 
        rw [hk, mul_zero, Eq.comm, sub_eq_zero] at h
        
        have even4c : ¬ Odd (4*↑↑c) := by
          rw [Nat.not_odd_iff_even, even_iff_two_dvd , show 4 = 2*2 by decide, mul_assoc]
          exact Nat.dvd_mul_right 2 (2 * ↑c)
        
        have odd4c : Odd (4 * ↑↑c):= by
          have h₀: Odd (p^2) := Odd.pow (Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_three hpmod3))
          rw[←pow_two] at h
          have h₁ := by apply congrArg (Odd ·) h
          norm_cast at h₁
          apply Eq.to_iff at h₁
          push_cast at h₁
          exact  h₁.mp h₀
        
        exact even4c odd4c

      replace h₂ : (a:ZMod p) ≠ 0 := by simpa[←ZMod.intCast_eq_intCast_iff] using h₂

      --  But $p \\equiv 3(\\bmod 4)$ and is therefore not the sum of two squares
      apply ZMod.mod_four_ne_three_of_sq_eq_neg_sq  h₂ h₁

    exact hpmod3' hpmod3