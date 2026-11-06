import Mathlib
import Aesop
open BigOperators

/- Fine all tuples of positive integers  $(a,b,c)$  such that  $\displaystyle lcm(a,b,c)=\frac{ab+bc+ca}{4}$ . -/
theorem number_theory_8680 :
    {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ Nat.lcm (Nat.lcm a b) c = (a * b + b * c + c * a : ℝ) / 4} = {(1, 2, 2), (2, 1, 2), (2, 2, 1)} := by
  ext x
  -- Technical lemma for LEAN proof.
  have get_terms (x y : ℕ × ℕ × ℕ) : x = y ↔ (x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2 = y.2.2) := by
    apply Iff.intro <;> intro h
    . tauto
    . calc
        x = (x.1, x.2.1, x.2.2) := by simp
        _ = (y.1, y.2.1, y.2.2) := by rw [h.1, h.2.1, h.2.2]
        _ = y := by simp
  -- WLOG: a ≤ b ≤ c and the theorem holds.
  have lm (a b c : ℕ): 0 < a ∧ a ≤ b ∧ b ≤ c ∧ (a.lcm b).lcm c = (a * b + b * c + c * a : ℝ) / 4 ↔ (a, b, c) = (1, 2, 2) := by
    apply Iff.intro <;> intro h
    . -- If 0 < a ≤ b ≤ c and lcm (a, b, c) = (ab + bc + ca) / 4, then (a, b, c) = (1, 2, 2).
      obtain ⟨h₀, h₁, h₂, h₃⟩ := h
      -- Show that c ∣ a * b.
      replace h₃ : 4 * (a.lcm b).lcm c = a * b + b * c + c * a := by
        rify
        field_simp at h₃
        ring_nf at h₃ ⊢
        exact h₃
      have h₄ : c ∣ a * b + b * c + c * a := by
        calc
          c ∣ (a.lcm b).lcm c := by apply Nat.dvd_lcm_right
          _ ∣ a * b + b * c + c * a := by rw [<-h₃]; apply Nat.dvd_mul_left
      replace h₄ : c ∣ a * b + (b * c + c * a) - (b * c + c * a) := by
        apply Nat.dvd_sub
        omega
        rw [<-add_assoc]
        assumption
        apply Nat.dvd_add
        apply Nat.dvd_mul_left
        apply Nat.dvd_mul_right
      replace h₄ : c ∣ a * b := by
        rwa [show a * b + (b * c + c * a) - (b * c + c * a) = a * b by apply Nat.add_sub_cancel] at h₄
      -- We have lcm (a, b, c) ∣ a * b.
      have h₅ : (a.lcm b).lcm c ∣ a * b := by
        apply Nat.lcm_dvd
        apply Nat.lcm_dvd
        apply Nat.dvd_mul_right
        apply Nat.dvd_mul_left
        assumption
      apply exists_eq_mul_left_of_dvd at h₅
      obtain ⟨k, h₅⟩ := h₅
      -- Show that lcm (a, b, c) = ab.
      have h₆ : 0 < k := by
        by_contra!
        nlinarith
      have h₇ : 3 * a * b ≤ 4 * (a.lcm b).lcm c := by
        calc
          3 * a * b = a * b + a * b + a * b := by ring_nf
          _ ≤ a * b + b * c + c * a := by nlinarith
          _ = 4 * (a.lcm b).lcm c := by symm; assumption
      replace h₇ : k < 2 := by
        by_contra!
        have false_eq : 6 * a * b ≤ 4 * a * b := by
          calc
            6 * a * b ≤ k * 3 * a * b := by nlinarith
            _ = k * (3 * a * b) := by ring_nf
            _ ≤ k * (4 * (a.lcm b).lcm c) := by nlinarith
            _ = 4 * (k * (a.lcm b).lcm c) := by ring_nf
            _ = 4 * a * b := by rw[<-h₅, mul_assoc]
        nlinarith
      replace h₆ : k = 1 := by
        omega
      clear h₇
      rw [h₆, one_mul] at h₅
      clear h₆
      -- Let k = ab / c and show that a + b = 3k.
      apply exists_eq_mul_left_of_dvd at h₄
      obtain ⟨k, h₄⟩ := h₄
      rw [<-h₅, show 4 * (a * b) = a * b + 3 * (a * b) by omega, add_assoc, h₄] at h₃
      apply Nat.add_left_cancel at h₃
      rw [<-mul_assoc] at h₃
      rw [show b * c + c * a = (b + a) * c by ring_nf] at h₃
      apply Nat.mul_right_cancel (show 0 < c by linarith) at h₃
      -- Lemma: For any prime p, the p-adic value of lcm (a, b, c) is equal to either that of a, b or c.
      have lm_lcm (a b c p : ℕ) (h₀ : 0 < a) (h₁ : 0 < b) (h₂ : 0 < c) [hp : Fact p.Prime] : padicValNat p ((a.lcm b).lcm c) = padicValNat p a ∨ padicValNat p ((a.lcm b).lcm c) = padicValNat p b ∨ padicValNat p ((a.lcm b).lcm c) = padicValNat p c := by
        have g₀ : a ∣ (a.lcm b).lcm c := by
          calc
            a ∣ a.lcm b := by apply Nat.dvd_lcm_left
            _ ∣ (a.lcm b).lcm c := by apply Nat.dvd_lcm_left
        have g₁ : b ∣ (a.lcm b).lcm c := by
          calc
            b ∣ a.lcm b := by apply Nat.dvd_lcm_right
            _ ∣ (a.lcm b).lcm c := by apply Nat.dvd_lcm_left
        have g₂ : c ∣ (a.lcm b).lcm c := by
          apply Nat.dvd_lcm_right
        apply exists_eq_mul_left_of_dvd at g₀
        apply exists_eq_mul_left_of_dvd at g₁
        apply exists_eq_mul_left_of_dvd at g₂
        obtain ⟨c₀, g₀⟩ := g₀
        obtain ⟨c₁, g₁⟩ := g₁
        obtain ⟨c₂, g₂⟩ := g₂
        have glcm : (a.lcm b).lcm c > 0 := by
          apply Nat.lcm_pos
          apply Nat.lcm_pos
          assumption'
        have g₃ : c₀ ≠ 0 := by
          by_contra!
          rw [this, zero_mul] at g₀
          linarith
        replace g₃ : c₀ ≥ 1 := by
          omega
        have g₄ : c₁ ≠ 0 := by
          by_contra!
          rw [this, zero_mul] at g₁
          linarith
        replace g₄ : c₁ ≥ 1 := by
          omega
        have g₅ : c₂ ≠ 0 := by
          by_contra!
          rw [this, zero_mul] at g₂
          linarith
        replace g₅ : c₂ ≥ 1 := by
          omega
        have g₆ : padicValNat p ((a.lcm b).lcm c) = padicValNat p c₀ + padicValNat p a := by
          rw [g₀]
          apply padicValNat.mul
          omega
          omega
        have g₇ : padicValNat p ((a.lcm b).lcm c) = padicValNat p c₁ + padicValNat p b := by
          rw [g₁]
          apply padicValNat.mul
          omega
          omega
        have g₈ : padicValNat p ((a.lcm b).lcm c) = padicValNat p c₂ + padicValNat p c := by
          rw [g₂]
          apply padicValNat.mul
          omega
          omega
        have h : padicValNat p c₀ = 0 ∨ padicValNat p c₁ = 0 ∨ padicValNat p c₂ = 0 := by
          by_contra!
          obtain ⟨g₆, g₇, g₈⟩ := this
          replace g₆ : 1 ≤ padicValNat p c₀ := by
            omega
          replace g₇ : 1 ≤ padicValNat p c₁ := by
            omega
          replace g₈ : 1 ≤ padicValNat p c₂ := by
            omega
          replace g₆ : p ∣ c₀ := by
            rw [show p = p ^ 1 by simp]
            rwa [padicValNat_dvd_iff_le]
            omega
          replace g₇ : p ∣ c₁ := by
            rw [show p = p ^ 1 by simp]
            rwa [padicValNat_dvd_iff_le]
            omega
          replace g₈ : p ∣ c₂ := by
            rw [show p = p ^ 1 by simp]
            rwa [padicValNat_dvd_iff_le]
            omega
          apply exists_eq_mul_right_of_dvd at g₆
          obtain ⟨d₀, g₆⟩ := g₆
          rw [g₆, mul_assoc] at g₀
          apply exists_eq_mul_right_of_dvd at g₇
          obtain ⟨d₁, g₇⟩ := g₇
          rw [g₇, mul_assoc] at g₁
          apply exists_eq_mul_right_of_dvd at g₈
          obtain ⟨d₂, g₈⟩ := g₈
          rw [g₈, mul_assoc] at g₂
          have g₉ : a ∣ (a.lcm b).lcm c / p := by
            calc
              a ∣ d₀ * a := by apply Nat.dvd_mul_left
              _ ∣ (a.lcm b).lcm c / p := by apply Nat.dvd_div_of_mul_dvd; rw [g₀]
          have g₁₀ : b ∣ (a.lcm b).lcm c / p := by
            calc
              b ∣ d₁ * b := by apply Nat.dvd_mul_left
              _ ∣ (a.lcm b).lcm c / p := by apply Nat.dvd_div_of_mul_dvd; rw [g₁]
          have g₁₁ : c ∣ (a.lcm b).lcm c / p := by
            calc
              c ∣ d₂ * c := by apply Nat.dvd_mul_left
              _ ∣ (a.lcm b).lcm c / p := by apply Nat.dvd_div_of_mul_dvd; rw [g₂]
          have g₁₂ : (a.lcm b).lcm c ∣ (a.lcm b).lcm c / p := by
            apply Nat.lcm_dvd
            apply Nat.lcm_dvd
            assumption'
          replace g₁₂ : (a.lcm b).lcm c ≤ (a.lcm b).lcm c / p := by
            apply Nat.le_of_dvd
            rw [g₀, mul_comm, Nat.mul_div_cancel]
            have h : d₀ > 0 := by
              by_contra!
              have h : d₀ = 0 := by
                omega
              rw [h, mul_zero] at g₆
              omega
            apply Nat.mul_pos
            assumption'
            apply Nat.Prime.pos
            exact hp.out
          replace false_eq : (a.lcm b).lcm c * 2 < (a.lcm b).lcm c * 2 := by
            calc
              (a.lcm b).lcm c * 2 ≤ (a.lcm b).lcm c * p := by apply Nat.mul_le_mul_left; apply Nat.Prime.two_le; exact hp.out
              _ ≤ (a.lcm b).lcm c / p * p := by apply Nat.mul_le_mul_right; exact g₁₂
              _ = (a.lcm b).lcm c := by rw [Nat.div_mul_cancel]; rw [g₀]; apply Nat.dvd_mul_right
              _ < (a.lcm b).lcm c * 2 := by omega
          linarith
        obtain g₉ | g₁₀ | g₁₁ := h
        left
        rw [g₉] at g₆
        rw [g₆, zero_add]
        right
        left
        rw [g₁₀] at g₇
        rw [g₇, zero_add]
        right
        right
        rw [g₁₁] at g₈
        rw [g₈, zero_add]
      -- Show that k = 1, so ab = c and a + b = 3.
      have h₇ : k = 1 := by
        by_contra!
        apply Nat.exists_prime_and_dvd at this
        obtain ⟨p, ⟨hp, h₆⟩⟩ := this
        replace hp : Fact p.Prime := by
          rw [fact_iff]
          exact hp
        have h_impos : padicValNat p ((a.lcm b).lcm c) = padicValNat p a ∨ padicValNat p ((a.lcm b).lcm c) = padicValNat p b ∨ padicValNat p ((a.lcm b).lcm c) = padicValNat p c := by
          apply lm_lcm
          all_goals omega
        obtain h_eqa | h_eqb | h_eqc := h_impos
        . -- Derive a contradiction when ν_p (a) = ν_p (ab).
          rw [<-h₅, padicValNat.mul, <-add_zero (padicValNat p a)] at h_eqa
          apply Nat.add_left_cancel at h_eqa
          have h₇ : p ∣ a * b := by
            calc
              p ∣ k := by assumption
              _ ∣ k * c := by apply Nat.dvd_mul_right
              _ = a * b := by rw [h₄]
          have h₈ : ¬p ∣ b := by
            by_contra h
            have _ : 1 ≤ padicValNat p b := by
              apply one_le_padicValNat_of_dvd
              omega
              exact h
            linarith
          have h₉ : p ∣ a := by
            apply Nat.Coprime.dvd_of_dvd_mul_right at h₇
            exact h₇
            rw [Nat.Prime.coprime_iff_not_dvd]
            exact h₈
            exact hp.out
          have h₁₀ : p ∣ b + a := by
            calc
              p ∣ k := by assumption
              _ ∣ 3 * k := by apply Nat.dvd_mul_left
              _ = b + a := by rw [h₃]
          replace h₁₀ : p ∣ b := by
            rw [show b = b + a - a by omega]
            apply Nat.dvd_sub (show a ≤ b + a by omega) h₁₀ h₉
          tauto
          omega
          omega
        . -- Derive a contradiction when ν_p (b) = ν_p (ab).
          rw [<-h₅, padicValNat.mul] at h_eqb
          nth_rewrite 2 [<-zero_add (padicValNat p b)] at h_eqb
          apply Nat.add_right_cancel at h_eqb
          have h₇ : p ∣ a * b := by
            calc
              p ∣ k := by assumption
              _ ∣ k * c := by apply Nat.dvd_mul_right
              _ = a * b := by rw [h₄]
          have h₈ : ¬p ∣ a := by
            by_contra h
            have _ : 1 ≤ padicValNat p a := by
              apply one_le_padicValNat_of_dvd
              omega
              exact h
            linarith
          have h₉ : p ∣ b := by
            apply Nat.Coprime.dvd_of_dvd_mul_left at h₇
            exact h₇
            rw [Nat.Prime.coprime_iff_not_dvd]
            exact h₈
            exact hp.out
          have h₁₀ : p ∣ a + b := by
            calc
              p ∣ k := by assumption
              _ ∣ 3 * k := by apply Nat.dvd_mul_left
              _ = a + b := by rw [h₃, add_comm]
          replace h₁₀ : p ∣ a := by
            rw [show a = a + b - b by omega]
            apply Nat.dvd_sub (show b ≤ a + b by omega) h₁₀ h₉
          tauto
          omega
          omega
        . -- Derive a contradiction when ν_p (c) = ν_p (ab).
          rw [<-h₅, h₄, padicValNat.mul] at h_eqc
          nth_rewrite 2 [<-zero_add (padicValNat p c)] at h_eqc
          apply Nat.add_right_cancel at h_eqc
          apply one_le_padicValNat_of_dvd at h₆
          all_goals omega
      -- Now a + b = 3, so we can try the cases.
      have b_eq : 2 * b ≥ 3 := by
        calc
          2 * b = b + b := by omega
          _ ≥ b + a := by omega
          _ = 3 := by rw [<-h₃, h₇]; norm_num
      replace b_eq : 2 * 1 < 2 * b := by
        omega
      replace b_eq : 1 < b := by
        nlinarith
      have b_eq : b = 2 := by
        omega
      have a_eq : a = 1 := by
        omega
      have c_eq : c = 2 := by
        rw [a_eq, b_eq, h₇] at h₄
        omega
      rw [get_terms]
      tauto
    . -- If (a, b, c) = (1, 2, 2), then 0 < a ≤ b ≤ c and lcm (a, b, c) = (ab + bc + ca) / 4.
      simp [get_terms] at h
      simp [show 0 < a by omega, show a ≤ b by omega, show b ≤ c by omega]
      obtain ⟨ha, hb, hc⟩ := h
      rw [ha, hb, hc]
      simp
      norm_num
  simp at lm ⊢
  -- Tree of decision:
    -- a ≤ b
      -- b ≤ c → a ≤ b ≤ c
      -- c < b
        -- c ≤ a → c ≤ a ≤ b
        -- a < c → a < c < b
      -- b < a
        -- b ≤ c
          -- c ≤ a → b ≤ c ≤ a
          -- a < c → b < a < c
        -- c < b → c < b < a
  by_cases g₀ : x.1 ≤ x.2.1
  . -- Case of a ≤ b.
    by_cases g₁ : x.2.1 ≤ x.2.2
    . -- Cases of b ≤ c.
      apply Iff.intro <;> intro h
      . replace h : 0 < x.1 ∧ x.1 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2 ∧ (x.1.lcm x.2.1).lcm x.2.2 = (x.1 * x.2.1 + x.2.1 * x.2.2 + x.2.2 * x.1 : ℝ) / 4 := by
          simp [show x.1 ≤ x.2.1 by omega, show x.2.1 ≤ x.2.2 by omega]
          tauto
        rw [lm x.1 x.2.1 x.2.2] at h
        left
        simp [get_terms]
        tauto
      . obtain h | h | h := h <;> (rw [get_terms] at h; simp at h; try omega)
        rw [<-lm x.1 x.2.1 x.2.2] at h
        simp [show 0 < x.2.1 by omega, show 0 < x.2.2 by omega]
        tauto
    . -- Cases of c < b.
      by_cases g₂ : x.2.2 ≤ x.1
      . -- Cases of c ≤ a.
        apply Iff.intro <;> intro h
        . replace h : 0 < x.2.2 ∧ x.2.2 ≤ x.1 ∧ x.1 ≤ x.2.1 ∧ (x.2.2.lcm x.1).lcm x.2.1 = (x.2.2 * x.1 + x.1 * x.2.1 + x.2.1 * x.2.2 : ℝ) / 4 := by
            simp [show x.2.2 ≤ x.1 by omega, show x.1 ≤ x.2.1 by omega]
            -- Rewrite ab + bc + ca by commutativity of multiplication and assocativity of addition.
            ring_nf at h ⊢
            rw [Nat.lcm_comm x.2.2 x.1, Nat.lcm_assoc, Nat.lcm_comm x.2.2 x.2.1, <-Nat.lcm_assoc]
            tauto
          rw [lm x.2.2 x.1 x.2.1] at h
          right
          right
          simp [get_terms]
          tauto
        . obtain h | h | h := h <;> (rw [get_terms] at h; simp at h; try omega)
          rw [show x.1 = 2 ∧ x.2.1 = 2 ∧ x.2.2 = 1 ↔ x.2.2 = 1 ∧ x.1 = 2 ∧ x.2.1 = 2 by tauto, <-lm x.2.2 x.1 x.2.1] at h
          simp [show 0 < x.1 by omega, show 0 < x.2.1 by omega]
          ring_nf at h ⊢
          rw [Nat.lcm_comm x.2.2 x.1, Nat.lcm_assoc, Nat.lcm_comm x.2.2 x.2.1, <-Nat.lcm_assoc] at h
          tauto
      . -- Cases of a < c.
        apply Iff.intro <;> intro h
        . replace h : 0 < x.1 ∧ x.1 ≤ x.2.2 ∧ x.2.2 ≤ x.2.1 ∧ (x.1.lcm x.2.2).lcm x.2.1 = (x.1 * x.2.2 + x.2.2 * x.2.1 + x.2.1 * x.1 : ℝ) / 4 := by
            simp [show x.1 ≤ x.2.2 by omega, show x.2.2 ≤ x.2.1 by omega]
            -- Rewrite ab + bc + ca by commutativity of multiplication and assocativity of addition.
            ring_nf at h ⊢
            rw [Nat.lcm_assoc, Nat.lcm_comm x.2.2 x.2.1, <-Nat.lcm_assoc]
            tauto
          rw [lm x.1 x.2.2 x.2.1] at h
          left
          simp [get_terms]
          tauto
        . obtain h | h | h := h <;> (rw [get_terms] at h; simp at h; try omega)
  . -- Cases of b < a.
    by_cases g₁ : x.2.1 ≤ x.2.2
    . -- Cases of b ≤ c.
      by_cases g₂ : x.2.2 ≤ x.1
      . -- Cases of c ≤ a.
        apply Iff.intro <;> intro h
        . replace h : 0 < x.2.1 ∧ x.2.1 ≤ x.2.2 ∧ x.2.2 ≤ x.1 ∧ (x.2.1.lcm x.2.2).lcm x.1 = (x.2.1 * x.2.2 + x.2.2 * x.1 + x.1 * x.2.1 : ℝ) / 4 := by
            simp [show x.2.1 ≤ x.2.2 by omega, show x.2.2 ≤ x.1 by omega]
            -- Rewrite ab + bc + ca by commutativity of multiplication and assocativity of addition.
            ring_nf at h ⊢
            rw [Nat.lcm_comm, <-Nat.lcm_assoc]
            tauto
          rw [lm x.2.1 x.2.2 x.1] at h
          right
          left
          simp [get_terms]
          tauto
        . obtain h | h | h := h <;> (rw [get_terms] at h; simp at h; try omega)
          rw [show x.1 = 2 ∧ x.2.1 = 1 ∧ x.2.2 = 2 ↔ x.2.1 = 1 ∧ x.2.2 = 2 ∧ x.1 = 2 by tauto, <-lm x.2.1 x.2.2 x.1] at h
          simp [show 0 < x.1 by omega, show 0 < x.2.2 by omega]
          ring_nf at h ⊢
          rw [Nat.lcm_comm, <-Nat.lcm_assoc] at h
          tauto
      . -- Cases of a < c.
        apply Iff.intro <;> intro h
        . replace h : 0 < x.2.1 ∧ x.2.1 ≤ x.1 ∧ x.1 ≤ x.2.2 ∧ (x.2.1.lcm x.1).lcm x.2.2 = (x.2.1 * x.1 + x.1 * x.2.2 + x.2.2 * x.2.1 : ℝ) / 4 := by
            simp [show x.2.1 ≤ x.1 by omega, show x.1 ≤ x.2.2 by omega]
            -- Rewrite ab + bc + ca by commutativity of multiplication and assocativity of addition.
            ring_nf at h ⊢
            rw [Nat.lcm_comm x.2.1 x.1]
            tauto
          rw [lm x.2.1 x.1 x.2.2] at h
          right
          left
          simp [get_terms]
          tauto
        . obtain h | h | h := h <;> (rw [get_terms] at h; simp at h; try omega)
    . -- Cases of c < b. x.2.2 < x.2.1 < x.1-/
      apply Iff.intro <;> intro h
      . replace h : 0 < x.2.2 ∧ x.2.2 ≤ x.2.1 ∧ x.2.1 ≤ x.1 ∧ (x.2.2.lcm x.2.1).lcm x.1 = (x.2.2 * x.2.1 + x.2.1 * x.1 + x.1 * x.2.2 : ℝ) / 4 := by
          simp [show x.2.2 ≤ x.2.1 by omega, show x.2.1 ≤ x.1 by omega]
          -- Rewrite ab + bc + ca by commutativity of multiplication and assocativity of addition.
          ring_nf at h ⊢
          rw [Nat.lcm_comm, Nat.lcm_comm x.2.2 x.2.1, <-Nat.lcm_assoc]
          tauto
        rw [lm x.2.2 x.2.1 x.1] at h
        right
        right
        simp [get_terms]
        tauto
      . obtain h | h | h := h <;> (rw [get_terms] at h; simp at h; try omega)
