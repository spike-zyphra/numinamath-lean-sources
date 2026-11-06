import Mathlib
set_option maxHeartbeats 99999999999999

lemma glcm_eq_zero_iff : Nat.lcm m n = 0 ↔ m = 0 ∨ n = 0 := by
  cases m <;> cases n <;> simp [Nat.lcm_ne_zero] at *

lemma encard_prod {α β : Type*} (a : Set α) (b : Set β) :
    (a ×ˢ b).encard = a.encard * b.encard := by
  obtain rfl | hae := a.eq_empty_or_nonempty
  · simp
  obtain rfl | hbe := b.eq_empty_or_nonempty
  · simp
  obtain ha | ha := a.infinite_or_finite
  · rw [(ha.prod_left hbe).encard_eq, ha.encard_eq, ENat.top_mul hbe.encard_pos.ne']
  obtain hb | hb := b.infinite_or_finite
  · rw [(hb.prod_right hae).encard_eq, hb.encard_eq, ENat.mul_top hae.encard_pos.ne']
  rw [ha.encard_eq_coe_toFinset_card, hb.encard_eq_coe_toFinset_card]
  rw [(ha.prod hb).encard_eq_coe_toFinset_card, ← ENat.coe_mul, ENat.coe_inj]
  rw [← ha.toFinset_prod hb, Finset.card_product]
lemma ncard_prod {α β : Type*} (a : Set α) (b : Set β) :
  (a ×ˢ b).ncard = a.ncard * b.ncard := by
  have toNat_mul (a b : ℕ∞) : (a * b).toNat = a.toNat * b.toNat := by
    cases a <;> cases b <;> simp
    · rename_i b; cases b <;> simp
    · rename_i a; cases a <;> simp
    · rw [← ENat.coe_mul, ENat.toNat_coe]
  simp [Set.ncard_def, encard_prod, toNat_mul]
lemma count_disjoint_max_card_eq (a : ℕ →₀ ℕ) :
  { (u, v) : (ℕ →₀ ℕ) × (ℕ →₀ ℕ) |
    u ⊓ v = 0 ∧ u ⊔ v = a }.ncard = 2 ^ a.support.card := by
  have im : Nat.card { (u, v) : (ℕ →₀ ℕ) × (ℕ →₀ ℕ) | u ⊓ v = 0 ∧ u ⊔ v = a } = Nat.card (Fin a.support.card → Bool) := by
    apply Nat.card_congr
    constructor
    pick_goal 3
    · exact fun ⟨⟨aa, ab⟩, haa⟩ bb => aa ((Finset.equivFin a.support).invFun bb) = 0
    pick_goal 3
    · exact fun test => ⟨⟨
        a.filter (fun x => if h : x ∈ a.support then ¬test ((Finset.equivFin a.support).toFun ⟨x, h⟩) else false),
        a.filter (fun x => if h : x ∈ a.support then test ((Finset.equivFin a.support).toFun ⟨x, h⟩) else false)⟩, by {
        simp; constructor
        all_goals ext n
        · simp [Finsupp.filter_apply]
          by_cases hh : a n = 0
          all_goals simp [hh]
        · simp [Finsupp.filter_apply]
          by_cases hh : n ∈ a.support
          · by_cases sc : test (a.support.equivFin ⟨n, hh⟩)
            all_goals simp [sc, hh]
            all_goals clear * -; tauto
          simp at hh
          all_goals simp [hh]
        }⟩
    · rintro ⟨⟨x, y⟩, hh⟩
      simp [Finsupp.filter_apply]
      constructor <;> ext j <;> simp [Finsupp.filter_apply] <;> simp at hh <;> obtain ⟨hh, uu⟩ := hh
      · apply_fun (fun x => x j) at hh uu
        simp at hh uu
        obtain hh | hh := hh
        · simp [hh]
        · simp [hh] at uu
          simp [uu]; tauto
      · apply_fun (fun x => x j) at hh uu
        simp at hh uu
        obtain hh | hh := hh
        · simp [hh] at uu
          simp [hh, uu]; tauto
        · simp [hh] at uu
          simp [uu]; tauto
    · intro xx
      simp [Finsupp.filter_apply]
      ext j
      have hrm : ↑(a.support.equivFin.symm j) ∈ a.support := by simp
      rw [Finsupp.mem_support_iff] at hrm
      simp [hrm]
  rw [Set.Nat.card_coe_set_eq] at im
  simp [im]

/- Determine the number of pairs of positive integers $x,y$ such that $x\le y$, $\gcd (x,y)=5!$ and $\text{lcm}(x,y)=50!$. -/
theorem number_theory_53765 :
  {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ x ≤ y ∧ Nat.gcd x y = Nat.factorial 5 ∧ Nat.lcm x y = Nat.factorial 50}.ncard = 16384 := by
  have xjs : {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ x ≤ y ∧ Nat.gcd x y = Nat.factorial 5 ∧ Nat.lcm x y = Nat.factorial 50}.ncard = {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ x ≤ y ∧ Nat.gcd x y = 1 ∧ Nat.lcm x y = Nat.factorial 50 / Nat.factorial 5}.ncard := by
    apply Set.ncard_congr (fun ⟨x, y⟩ hx => ⟨x / Nat.factorial 5, y / Nat.factorial 5⟩)
    all_goals simp
    · intros a b ha hb hab hc hd
      constructor
      · constructor
        · -- Show that 0 < 5!
          positivity
        · -- Show that 5! ≤ a
          have h1 : Nat.factorial 5 ∣ a := by 
            rw [←hc]
            apply Nat.gcd_dvd_left
          exact Nat.le_of_dvd (by positivity) h1
      constructor
      · constructor
        · -- Show that $0 < 5!$
          positivity
        · -- Show that $5! \leq b$
          have h1 : a.gcd b ∣ b := by exact Nat.gcd_dvd_right a b
          rw [hc] at h1
          exact Nat.le_of_dvd (by positivity) h1
      constructor
      · have h1 : 0 < Nat.factorial 5 := by
          apply Nat.factorial_pos
          all_goals omega
        apply Nat.div_le_div
        exact hab
        all_goals linarith
      obtain ⟨tt, ff⟩ := Nat.gcd_dvd a b
      simp only [hc] at tt ff
      rw [Nat.lcm.eq_1, Nat.gcd_div tt ff]
      rw [Nat.lcm.eq_1] at hd
      obtain ⟨t, tt⟩ := tt; obtain ⟨f, ff⟩ := ff
      constructor
      · rw [hc]; decide
      subst a b
      simp [Nat.mul_div_cancel_left _ (by decide : 0 < Nat.factorial 5), Nat.gcd_mul_left] at *
      simp only [(by decide : Nat.factorial 5 = 120)] at *
      have jj : t.gcd f = 1 := by omega
      simp [jj] at *
      rw [mul_assoc, Nat.mul_div_cancel_left _ (by decide)] at hd
      have qq : 120 ∣ Nat.factorial 50 := by native_decide
      rw [← hd]
      clear * -
      rw [Nat.mul_div_assoc, Nat.mul_div_cancel_left]
      · decide
      · exact Nat.dvd_mul_right 120 f
    · -- Note that this theorem is vacuously true because Lean 4 will compute the values and check that they are equal
      -- Lean will find that a.gcd b = 120 and a.lcm b = 50! must satisfy the divisibility conditions uniquely.
      -- Therefore, once a, b, a_1, b_1 satisfy the conditions given, they must be equal.
      -- Lean's arithmetic solver will check this from the definitions of gcd and lcm.
      -- Lean is able to solve this theorem directly because we have a/gcd(a,b) = a_1/gcd(a_1,b_1) and b/gcd(a,b) = b_1/gcd(a_1,b_1)
      -- Lean will verify that this implies a = a_1 and b = b_1
      -- Let's take the Lean proof approach directly:
      -- We have imported Mathlib to access factorial definitions and arithmetic tools.
      -- We can now directly use Lean's theorem proving capability to solve this theorem:
      -- After substitution of factorial values, we get:
      -- factorial 5 = 120
      -- factorial 50 = 50!
      -- Lean will compute these values and check the divisibility conditions
      -- Lean will find that the divisibility conditions (a/gcd(a,b) = a_1/gcd(a_1,b_1) and b/gcd(a,b) = b_1/gcd(a_1,b_1)) plus the gcd and lcm conditions must imply a = a_1 and b = b_1
      -- Lean will directly solve this from arithmetic:
      -- Assume all the conditions given and conclude a = a_1 and b = b_1
      -- Therefore, Lean's proof is:
      intros a b a_1 b_1 ha hb hab h1 h2 ha1 hb1 ha1b1 h11 h21 h3 h4
      have h5 : a = a_1 := by
        -- Since $a / 120 = a_1 / 120$ and $a$ and $a_1$ are positive, it follows that $a = a_1$
        have pos1 : a.gcd b ∣ a := by exact Nat.gcd_dvd_left a b
        have pos2 : a.gcd b ∣ b := by exact Nat.gcd_dvd_right a b
        have pos3 : a_1.gcd b_1 ∣ a_1 := by exact Nat.gcd_dvd_left a_1 b_1
        have pos4 : a_1.gcd b_1 ∣ b_1 := by exact Nat.gcd_dvd_right a_1 b_1
        -- Given that a.gcd b = 120 and a_1.gcd b_1 = 120
        rw [h1] at pos1 pos2
        rw [h11] at pos3 pos4
        -- Lean's simplifier will rewrite the factorial expressions
        -- Lean can compute factorial 5 and factorial 50 to get concrete numbers
        simp [Nat.factorial] at pos1 pos2 pos3 pos4 h3 h4
        -- After simplification, Lean will be able to derive that a = a_1 from h3 and b = b_1 from h4
        -- Lean's arithmetic solver can confirm that these divisibility conditions with the constraints given must mean a = a_1 and b = b_1
        -- Lean's theorem prover confirms that once we have a/120 = a_1/120 and b/120 = b_1/120, with all the divisibility constraints, a = a_1 and b = b_1 must hold
        -- This would be because a and a_1 are multiples of 120, so a = 120 * k and a_1 = 120 * k for some k, hence a = a_1, and similarly for b and b_1
        -- Lean's theorem prover confirms that once we have the divisibility conditions, and the numbers involved satisfy the constraints, a = a_1 and b = b_1 must hold
        omega
      -- Lean's omega tactic is able to solve this because it can determine that the equalities of the quotients (a / 120 = a_1 / 120 and b / 120 = b_1 / 120) combined with the arithmetic constraints given by the GCD and LCM imply a = a_1 and b = b_1
      have h6 : b = b_1 := by
        have pos1 : a.gcd b ∣ a := by exact Nat.gcd_dvd_left a b
        have pos2 : a.gcd b ∣ b := by exact Nat.gcd_dvd_right a b
        have pos3 : a_1.gcd b_1 ∣ a_1 := by exact Nat.gcd_dvd_left a_1 b_1
        have pos4 : a_1.gcd b_1 ∣ b_1 := by exact Nat.gcd_dvd_right a_1 b_1
        rw [h1] at pos1 pos2
        rw [h11] at pos3 pos4
        simp [Nat.factorial] at pos1 pos2 pos3 pos4 h3 h4
        omega
      -- Lean's omega tactic here is using the arithmetic relationships in the constraints and the equalities of the quotients to derive the equalities of the original numbers. Since the division operations preserve the equality when the divisor (120) is non-zero, and Lean's arithmetic solver confirms that with the given constraints, this implies a = a_1 and b = b_1.
      exact ⟨h5, h6⟩
    · intro a b h₀ h₁ h₂ h₃ h₄
      have h₅ : 0 < Nat.factorial 5 := by
        apply Nat.factorial_pos
        <;> norm_num
      
      have h₆ : 0 < Nat.factorial 50 := by
        apply Nat.factorial_pos
        <;> norm_num
      
      have h₇ : ∃ a_6 b_1, (0 < a_6 ∧ 0 < b_1 ∧ a_6 ≤ b_1 ∧ a_6.gcd b_1 = Nat.factorial 5 ∧ a_6.lcm b_1 = Nat.factorial 50) ∧ a_6 / Nat.factorial 5 = a ∧ b_1 / Nat.factorial 5 = b := by
        use a * Nat.factorial 5, b * Nat.factorial 5
        constructor
        · -- Prove the first part of the conjunction: 0 < a_6 ∧ 0 < b_1 ∧ a_6 ≤ b_1 ∧ a_6.gcd b_1 = Nat.factorial 5 ∧ a_6.lcm b_1 = Nat.factorial 50
          have h₇₁ : 0 < a * Nat.factorial 5 := by
            -- Prove that 0 < a * Nat.factorial 5
            have h₇₁₁ : 0 < a := h₀
            have h₇₁₂ : 0 < Nat.factorial 5 := h₅
            nlinarith
          have h₇₂ : 0 < b * Nat.factorial 5 := by
            -- Prove that 0 < b * Nat.factorial 5
            have h₇₂₁ : 0 < b := h₁
            have h₇₂₂ : 0 < Nat.factorial 5 := h₅
            nlinarith
          have h₇₃ : a * Nat.factorial 5 ≤ b * Nat.factorial 5 := by
            -- Prove that a * Nat.factorial 5 ≤ b * Nat.factorial 5
            have h₇₃₁ : a ≤ b := h₂
            have h₇₃₂ : 0 < Nat.factorial 5 := h₅
            nlinarith
          have h₇₄ : (a * Nat.factorial 5).gcd (b * Nat.factorial 5) = Nat.factorial 5 := by
            -- Prove that (a * Nat.factorial 5).gcd (b * Nat.factorial 5) = Nat.factorial 5
            have h₇₄₁ : a.gcd b = 1 := h₃
            have h₇₄₂ : (a * Nat.factorial 5).gcd (b * Nat.factorial 5) = (a.gcd b) * Nat.factorial 5 := by
              rw [Nat.gcd_mul_right, Nat.gcd_comm]
              <;> simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
              <;>
              ring_nf at *
              <;>
              simp_all [Nat.gcd_mul_right, Nat.gcd_mul_left, Nat.gcd_comm]
              <;>
              ring_nf at *
              <;>
              simp_all [Nat.gcd_mul_right, Nat.gcd_mul_left, Nat.gcd_comm]
            rw [h₇₄₂, h₇₄₁]
            <;> simp [h₅]
            <;> ring_nf at *
            <;> simp_all
          have h₇₅ : (a * Nat.factorial 5).lcm (b * Nat.factorial 5) = Nat.factorial 50 := by
            -- Prove that (a * Nat.factorial 5).lcm (b * Nat.factorial 5) = Nat.factorial 50
            have h₇₅₁ : a.lcm b = Nat.factorial 50 / Nat.factorial 5 := h₄
            have h₇₅₂ : (a * Nat.factorial 5).lcm (b * Nat.factorial 5) = Nat.factorial 50 := by
              have h₇₅₃ : a.gcd b = 1 := h₃
              have h₇₅₄ : (a * Nat.factorial 5).lcm (b * Nat.factorial 5) = (a.lcm b) * Nat.factorial 5 := by
                have h₇₅₅ : a.lcm b = a * b := by
                  rw [Nat.lcm]
                  have h₇₅₆ : a.gcd b = 1 := h₃
                  have h₇₅₇ : a * b / a.gcd b = a * b := by
                    rw [h₇₅₆]
                    <;> simp [Nat.mul_div_cancel_left]
                    <;> nlinarith
                  rw [h₇₅₇]
                have h₇₅₈ : (a * Nat.factorial 5).lcm (b * Nat.factorial 5) = (a * Nat.factorial 5 * (b * Nat.factorial 5)) / (a * Nat.factorial 5).gcd (b * Nat.factorial 5) := by
                  rw [Nat.lcm]
                rw [h₇₅₈]
                have h₇₅₉ : (a * Nat.factorial 5).gcd (b * Nat.factorial 5) = Nat.factorial 5 := h₇₄
                rw [h₇₅₉]
                have h₇₅₁₀ : a * Nat.factorial 5 * (b * Nat.factorial 5) = (a * b) * (Nat.factorial 5 * Nat.factorial 5) := by
                  ring
                rw [h₇₅₁₀]
                have h₇₅₁₁ : (a * b) * (Nat.factorial 5 * Nat.factorial 5) / Nat.factorial 5 = (a * b) * Nat.factorial 5 := by
                  have h₇₅₁₂ : Nat.factorial 5 > 0 := h₅
                  have h₇₅₁₃ : (a * b) * (Nat.factorial 5 * Nat.factorial 5) = (a * b) * Nat.factorial 5 * Nat.factorial 5 := by
                    ring
                  rw [h₇₅₁₃]
                  have h₇₅₁₄ : (a * b) * Nat.factorial 5 * Nat.factorial 5 / Nat.factorial 5 = (a * b) * Nat.factorial 5 := by
                    apply Nat.mul_div_cancel _ h₇₅₁₂
                  rw [h₇₅₁₄]
                rw [h₇₅₁₁]
                have h₇₅₁₅ : a.lcm b * Nat.factorial 5 = (a * b) * Nat.factorial 5 := by
                  have h₇₅₁₆ : a.lcm b = a * b := by
                    rw [Nat.lcm]
                    have h₇₅₁₇ : a.gcd b = 1 := h₃
                    have h₇₅₁₈ : a * b / a.gcd b = a * b := by
                      rw [h₇₅₁₇]
                      <;> simp [Nat.mul_div_cancel_left]
                      <;> nlinarith
                    rw [h₇₅₁₈]
                  rw [h₇₅₁₆]
                  <;> ring
                rw [h₇₅₁₅]
              rw [h₇₅₄]
              have h₇₅₅ : a.lcm b = Nat.factorial 50 / Nat.factorial 5 := h₄
              rw [h₇₅₅]
              have h₇₅₆ : (Nat.factorial 50 / Nat.factorial 5) * Nat.factorial 5 = Nat.factorial 50 := by
                have h₇₅₇ : Nat.factorial 5 ∣ Nat.factorial 50 := by
                  apply Nat.dvd_of_mod_eq_zero
                  <;> rfl
                have h₇₅₈ : (Nat.factorial 50 / Nat.factorial 5) * Nat.factorial 5 = Nat.factorial 50 := by
                  apply Nat.div_mul_cancel h₇₅₇
                rw [h₇₅₈]
              rw [h₇₅₆]
            rw [h₇₅₂]
          exact ⟨h₇₁, h₇₂, h₇₃, h₇₄, h₇₅⟩
        · -- Prove the second part of the conjunction: a_6 / Nat.factorial 5 = a ∧ b_1 / Nat.factorial 5 = b
          constructor
          · -- Prove that a_6 / Nat.factorial 5 = a
            have h₇₆ : (a * Nat.factorial 5) / Nat.factorial 5 = a := by
              have h₇₆₁ : 0 < Nat.factorial 5 := h₅
              have h₇₆₂ : (a * Nat.factorial 5) / Nat.factorial 5 = a := by
                rw [Nat.mul_div_cancel]; assumption
              exact h₇₆₂
            exact h₇₆
          · -- Prove that b_1 / Nat.factorial 5 = b
            have h₇₇ : (b * Nat.factorial 5) / Nat.factorial 5 = b := by
              have h₇₇₁ : 0 < Nat.factorial 5 := h₅
              have h₇₇₂ : (b * Nat.factorial 5) / Nat.factorial 5 = b := by
                rw [Nat.mul_div_cancel]; assumption
              exact h₇₇₂
            exact h₇₇
      exact h₇
  rw [xjs]
  clear xjs
  -- now we relate this to the factorization
  have dk := count_disjoint_max_card_eq (Nat.factorial 50 / Nat.factorial 5).factorization
  rw [(by native_decide : 2 ^ (Nat.factorial 50 / Nat.factorial 5).factorization.support.card = 32768)] at dk
  -- next do some ncard prod
  have skx : Set.ncard ({(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ x ≤ y ∧ x.gcd y = 1 ∧ x.lcm y = Nat.factorial 50 / Nat.factorial 5} ×ˢ ({0, 1} : Set ℕ)) = Set.ncard {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ x.gcd y = 1 ∧ x.lcm y = Nat.factorial 50 / Nat.factorial 5} := by
    apply Set.ncard_congr (fun ⟨⟨a, b⟩, c⟩ ha => if c = 1 then ⟨b, a⟩ else ⟨a, b⟩)
    · simp
      intros a b ha hb hc hab hac hbc as
      obtain rfl | rfl := as
      all_goals simp [hb, hc, hab, hac, hbc]
      rw [Nat.gcd_comm, Nat.lcm_comm]
      tauto
    · simp
      intros a b ha hb hc hab hac hbc as xs nx sk xk wi ir wo jk xx
      obtain rfl | rfl := sk
      all_goals obtain rfl | rfl := xx
      all_goals simp
      pick_goal 3; · omega
      all_goals rw [←nx] at jk
      all_goals have mxc : 1 < a.lcm b := by rw [nx]; native_decide
      all_goals clear nx
      · intro h
        have h₁ : hb * hc = a * b := by
          have h₄ : hb.lcm hc = hb * hc := by
            rw [Nat.lcm]
            <;> simp [wo, Nat.gcd_mul_left, Nat.gcd_mul_right, Nat.div_eq_of_eq_mul_left (show 0 < hb.gcd hc by
              have h₅ : 0 < hb.gcd hc := by simp [wo, Nat.gcd_pos_of_pos_left _ xk]
              linarith)]
            <;> ring
            <;> simp [wo, Nat.mul_div_cancel_left]
          have h₅ : a.lcm b = a * b := by
            rw [Nat.lcm]
            <;> simp [xs, Nat.gcd_mul_left, Nat.gcd_mul_right, Nat.div_eq_of_eq_mul_left (show 0 < a.gcd b by
              have h₅ : 0 < a.gcd b := by
                have h₅ : a.gcd b ≠ 0 := by
                  intro h₅
                  simp_all
                have h₆ : 0 < a.gcd b := Nat.pos_of_ne_zero h₅
                linarith
              linarith)]
            <;> ring
            <;> simp [xs, Nat.mul_div_cancel_left]
          have h₆ : hb * hc = a * b := by
            nlinarith
          exact h₆
        
        have h₂ : hb = b := by
          have h₂₁ : hb * a = a * b := by
            have h₂₂ : a = hc := h
            rw [h₂₂] at *
            nlinarith
          -- Since a > 0, we can divide both sides by a to get hb = b.
          have h₂₃ : hb = b := by
            apply Nat.eq_of_mul_eq_mul_left hac
            nlinarith
          exact h₂₃
        
        have h₃ : ¬b = hb := by
          intro h₄
          have h₅ : b = hb := h₄
          have h₆ : a = b := by
            have h₇ : a ≤ b := as
            have h₈ : hb ≤ hc := ir
            have h₉ : a = hc := h
            have h₁₀ : hb = b := h₂
            have h₁₁ : hb ≤ hc := ir
            have h₁₂ : a ≤ b := as
            nlinarith
          have h₇ : a = 1 := by
            have h₇₁ : a.gcd b = 1 := xs
            have h₇₂ : a = b := h₆
            have h₇₃ : a.gcd a = 1 := by simpa [h₇₂] using h₇₁
            have h₇₄ : a = 1 := by
              by_contra h₇₄
              have h₇₅ : a > 1 := by
                have h₇₅₁ : a ≠ 0 := by linarith
                have h₇₅₂ : a ≠ 1 := h₇₄
                omega
              have h₇₆ : a.gcd a = a := by
                apply Nat.gcd_eq_right
                simp
              omega
            exact h₇₄
          have h₈ : b = 1 := by
            have h₈₁ : a = b := h₆
            have h₈₂ : a = 1 := h₇
            linarith
          have h₉ : a.lcm b = 1 := by
            have h₉₁ : a = 1 := h₇
            have h₉₂ : b = 1 := h₈
            rw [h₉₁, h₉₂]
            <;> simp [Nat.lcm]
            <;> simp_all
          have h₁₀ : 1 < a.lcm b := mxc
          linarith
        have h₄ : ¬b = hb := h₃
        exact h₄
      · intro h1
        intro h2
        have h3 : hc ≤ hb := by
          have h3₁ : a = hc := h2
          have h3₂ : b = hb := h1
          have h3₃ : a ≤ b := as
          have h3₄ : hc ≤ hb := by
            rw [h3₁, h3₂] at h3₃
            exact h3₃
          exact h3₄
        
        have h4 : hb = hc := by
          have h4₁ : hb ≤ hc := ir
          have h4₂ : hc ≤ hb := h3
          have h4₃ : hb = hc := by
            apply le_antisymm
            · exact h4₁
            · exact h4₂
          exact h4₃
        
        have h5 : hb = 1 := by
          have h5₁ : hb.gcd hc = 1 := wo
          have h5₂ : hb = hc := h4
          have h5₃ : hb.gcd hc = hb := by
            rw [h5₂]
            <;> simp [Nat.gcd_self]
          have h5₄ : hb = 1 := by
            linarith
          exact h5₄
        
        have h6 : hc = 1 := by
          have h6₁ : hb = hc := h4
          have h6₂ : hb = 1 := h5
          linarith
        
        have h7 : a.lcm b = 1 := by
          have h7₁ : hb.lcm hc = a.lcm b := jk
          have h7₂ : hb.lcm hc = 1 := by
            rw [h5, h6]
            <;> simp [Nat.lcm]
          linarith
        
        have h8 : False := by
          have h8₁ : 1 < a.lcm b := mxc
          have h8₂ : a.lcm b = 1 := h7
          linarith
        exact False.elim h8
    · simp
      intro a b h₀ h₁ h₂ h₃
      have h_main : ∃ a_5 b_1 b_2, ((0 < a_5 ∧ 0 < b_1 ∧ a_5 ≤ b_1 ∧ a_5.gcd b_1 = 1 ∧ a_5.lcm b_1 = Nat.factorial 50 / Nat.factorial 5) ∧ (b_2 = 0 ∨ b_2 = 1)) ∧ (if b_2 = 1 then (b_1, a_5) else (a_5, b_1)) = (a, b) := by
        -- Case analysis on a ≤ b or a > b
        by_cases h : a ≤ b
        · -- Case a ≤ b
          refine' ⟨a, b, 0, ⟨⟨h₀, h₁, h, by simpa [Nat.gcd_comm] using h₂, by simpa [Nat.lcm_comm] using h₃⟩, _⟩, _⟩
          · -- Prove b₂ = 0 ∨ b₂ = 1
            simp
          · -- Prove the if-then-else condition
            simp [h]
        · -- Case a > b
          have h' : b ≤ a := by omega
          refine' ⟨b, a, 1, ⟨⟨h₁, h₀, h', _⟩, _⟩, _⟩
          · rw [Nat.gcd_comm, Nat.lcm_comm]
            tauto
          · -- Prove b₂ = 0 ∨ b₂ = 1
            simp
          · -- Prove the if-then-else condition
            simp [Nat.lt_of_le_of_ne, Nat.le_of_lt_succ, h]
            <;> simp_all [Nat.gcd_comm, Nat.lcm_comm, Prod.ext_iff]
            <;> omega
      exact h_main
  -- now we rewrite the multiplication
  rw [ncard_prod, (by simp : Set.ncard {0, 1} = 2)] at skx
  have mds : Set.ncard {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ x.gcd y = 1 ∧ x.lcm y = Nat.factorial 50 / Nat.factorial 5} = {(u, v) | u ⊓ v = 0 ∧ u ⊔ v = (Nat.factorial 50 / Nat.factorial 5).factorization}.ncard := by
    apply Set.ncard_congr (fun ⟨x, y⟩ xm => ⟨Nat.factorization x, Nat.factorization y⟩)
    all_goals simp
    pick_goal 3
    · intros a b h1 h2
      exists a.prod fun x1 x2 => x1 ^ x2, b.prod fun x1 x2 => x1 ^ x2
      have ald : ∀ p ∈ b.support, Nat.Prime p := by
        intro p hp
        have slx : p ∈ (a ⊔ b).support := by simp [hp]
        rw [h2, Nat.support_factorization] at slx
        apply Nat.prime_of_mem_primeFactors at slx
        exact slx
      have dks : ∀ p ∈ a.support, Nat.Prime p := by
        intro p hp
        have slx : p ∈ (a ⊔ b).support := by simp [hp]
        rw [h2, Nat.support_factorization] at slx
        apply Nat.prime_of_mem_primeFactors at slx
        exact slx
      simp [Nat.prod_pow_factorization_eq_self ald, Nat.prod_pow_factorization_eq_self dks]
      have ssx : 0 ∉ (a ⊔ b).support := by
        rw [h2]; simp; decide
      have dls : 0 ∉ a.support := by simp; simp at ssx; clear * - ssx; omega
      have dss : 0 ∉ b.support := by simp; simp at ssx; clear * - ssx; omega
      have uu := Nat.prod_pow_pos_of_zero_not_mem_support dls
      have ii := Nat.prod_pow_pos_of_zero_not_mem_support dss
      simp [Nat.prod_pow_pos_of_zero_not_mem_support dls, Nat.prod_pow_pos_of_zero_not_mem_support dss]
      constructor
      · apply Nat.factorization_inj
        · simp
          intro sa
          rw [Nat.gcd_eq_zero_iff] at sa
          linarith
        · decide
        simp [Nat.factorization_gcd (by rw [Nat.ne_zero_iff_zero_lt]; exact uu) (by rw [Nat.ne_zero_iff_zero_lt]; exact ii), Nat.prod_pow_factorization_eq_self ald, Nat.prod_pow_factorization_eq_self dks, h1]
      · apply Nat.factorization_inj
        · simp
          intro sa
          rw [glcm_eq_zero_iff] at sa
          omega
        · decide
        simp [Nat.factorization_lcm (by rw [Nat.ne_zero_iff_zero_lt]; exact uu) (by rw [Nat.ne_zero_iff_zero_lt]; exact ii), Nat.prod_pow_factorization_eq_self ald, Nat.prod_pow_factorization_eq_self dks, h2]
    all_goals intros a b ha hb
    all_goals try rw [← @Nat.factorization_gcd a b (by linarith) (by linarith)]
    all_goals try rw [← @Nat.factorization_lcm a b (by linarith) (by linarith)]
    · intros hc hd
      rw [hc, hd]
      simp
    · intros h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
      constructor
      all_goals apply Nat.factorization_inj (by simp; omega) (by simp; omega)
      all_goals assumption
  rw [dk, ← skx] at mds
  omega
