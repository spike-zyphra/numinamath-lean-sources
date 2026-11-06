import Mathlib

/- Remark: replace all pow_le_pow_left₀ by pow_le_pow_left in online system. -/

/- Find all triples $(a, b, c)$ of positive integers such that $a^{3}+b^{3}+c^{3}=(a b c)^{2}$. (Nigeria) -/
theorem number_theory_23788 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 3 + b ^ 3 + c ^ 3 = (a * b * c) ^ 2 ↔ (a, b, c) = (1, 2, 3) ∨ (a, b, c) = (1, 3, 2) ∨ (a, b, c) = (2, 1, 3) ∨ (a, b, c) = (2, 3, 1) ∨ (a, b, c) = (3, 1, 2) ∨ (a, b, c) = (3, 2, 1) := by
  -- Break the iff into two implications.
  apply Iff.intro <;> intro h
  . -- First, we show that a ^ 3 + b ^ 3 + c ^ 3 = (a * b * c) ^ 2 implies the six triples.
    simp
    -- WLOG b ≤ a.
    wlog hab : b ≤ a with h₀
    . -- The other case is by symmetry.
      simp [le_total a b] at hab
      replace h : b ^ 3 + a ^ 3 + c ^ 3 = (a * b * c) ^ 2 := by
        rw [<-h]
        ac_rfl
      replace h : b ^ 3 + a ^ 3 + c ^ 3 = (b * a * c) ^ 2 := by
        rw [h]
        ac_rfl
      have g := h₀ b a c hb ha hc h (le_of_lt hab)
      obtain g | g | g | g | g | g := g
      . right
        right
        left
        tauto
      . right
        right
        right
        right
        left
        tauto
      . left
        tauto
      . right
        right
        right
        right
        right
        tauto
      . right
        left
        tauto
      . right
        right
        right
        left
        tauto
    . -- WLOG c ≤ b.
      wlog hbc : c ≤ b with h₀
      . -- The other case is by symmetry.
        simp [le_total b c] at hbc
        cases le_total a c with
        | inl hac =>
          replace h : c ^ 3 + a ^ 3 + b ^ 3 = (a * b * c) ^ 2 := by
            rw [<-h]
            ac_rfl
          replace h : c ^ 3 + a ^ 3 + b ^ 3 = (c * a * b) ^ 2 := by
            rw [h]
            ac_rfl
          have g := h₀ c a b hc ha hb h hac hab
          obtain g | g | g | g | g | g := g
          . right
            right
            right
            left
            tauto
          . right
            right
            right
            right
            right
            tauto
          . right
            left
            tauto
          . right
            right
            right
            right
            left
            tauto
          . left
            tauto
          . right
            right
            left
            tauto
        | inr hac =>
          replace h : a ^ 3 + c ^ 3 + b ^ 3 = (a * b * c) ^ 2 := by
            rw [<-h]
            ac_rfl
          replace h : a ^ 3 + c ^ 3 + b ^ 3 = (a * c * b) ^ 2 := by
            rw [h]
            ac_rfl
          have g := h₀ a c b ha hc hb h hac (le_of_lt hbc)
          obtain g | g | g | g | g | g := g
          . tauto
          . tauto
          . tauto
          . tauto
          . tauto
          . have : a = 3 ∧ b = 1 ∧ c = 2 := by tauto
            simp [this]
      . -- We prove first that c = 1.
        have h₀ : a ^ 2 * (b ^ 2 * c ^ 2) > a ^ 2 * a := by
          calc
            a ^ 2 * (b ^ 2 * c ^ 2) = a ^ 3 + b ^ 3 + c ^ 3 := by rw [h]; ring
            _ > a ^ 3 := by rw [gt_iff_lt, add_assoc]; apply lt_add_of_pos_right; positivity
            _ = a ^ 2 * a := by ring
        rw [gt_iff_lt, mul_lt_mul_left (by positivity)] at h₀
        have h₁ : a ^ 2 * (3 * a) ≥ a ^ 2 * (b ^ 2 * c ^ 2) := by
          calc
            a ^ 2 * (3 * a) = a ^ 3 + a ^ 3 + a ^ 3 := by ring
            _ ≥ (a * b * c) ^ 2 := by rw [<-h]; apply add_le_add; apply add_le_add_left; apply pow_le_pow_left₀ (le_of_lt hb) hab; apply pow_le_pow_left₀ (le_of_lt hc) (hbc.trans hab)
            _ = a ^ 2 * (b ^ 2 * c ^ 2) := by ring
        rw [ge_iff_le, mul_le_mul_left (by positivity)] at h₁
        have h₂ : a ^ 3 + (b ^ 3 + c ^ 3) = a ^ 3 + a ^ 2 * (b ^ 2 * c ^ 2 - a) := by
          ring_nf
          nth_rewrite 4 [show 3 = 2 + 1 by norm_num]
          rw [pow_add, <-mul_add]
          simp
          rw [Nat.sub_add_cancel (le_of_lt h₀), h]
          ring
        simp at h₂
        have h₃ : 18 * b ^ 3 ≥ c ^ 5 * b ^ 3 := by
          calc
            18 * b ^ 3 = 9 * (b ^ 3 + b ^ 3) := by ring
            _ ≥ 9 * (b ^ 3 + c ^ 3) := by rw [ge_iff_le, mul_le_mul_left (by norm_num)]; apply add_le_add_left; apply pow_le_pow_left₀ (le_of_lt hc) hbc
            _ = 9 * (a ^ 2 * (b ^ 2 * c ^ 2 - a)) := by simp [h₂]
            _ ≥ 9 * (a ^ 2 * 1) := by rw [ge_iff_le, mul_le_mul_left (by norm_num), mul_le_mul_left (by positivity)]; omega
            _ = (3 * a) ^ 2 := by ring
            _ ≥ (b ^ 2 * c ^ 2) ^ 2 := by apply pow_le_pow_left₀ (by positivity) h₁
            _ = (b ^ 3 * c ^ 4) * b := by ring
            _ ≥ (b ^ 3 * c ^ 4) * c := by rw [ge_iff_le, mul_le_mul_left (by positivity)]; exact hbc
            _ = c ^ 5 * b ^ 3 := by ring
        simp at h₃
        rw [mul_le_mul_right (by positivity)] at h₃
        replace hc : c = 1 := by
          by_contra!
          replace this : 2 ≤ c := by
            omega
          have weq : 32 ≤ 18 := by
            calc
              32 = 2 ^ 5 := by norm_num
              _ ≤ c ^ 5 := by apply Nat.pow_le_pow_of_le_left this
              _ ≤ 18 := h₃
          norm_num at weq
        clear h₃
        -- Note that a > b, otherwise 2b³ + 1 = b⁴, which has no integer solution.
        replace hab : a > b := by
          by_contra!
          replace hab : a = b := by
            omega
          have h₄ : 2 * b ^ 3 + 1 = b ^ 4 := by
            rw [hab, hc] at h
            ring_nf at h ⊢
            exact h
          have hb' : b > 2 := by
            by_contra! this
            interval_cases b
            . norm_num at h₄
            . norm_num at h₄
          -- We have 2b³ + 1 < b⁴, which is a contradiction.
          have h₅ : 2 * b ^ 3 + 1 < b ^ 4 := by
            calc
              2 * b ^ 3 + 1 < 2 * b ^ 3 + b ^ 3 := by apply add_lt_add_left; norm_num; omega
              _ = 3 * b ^ 3 := by ring
              _ ≤ b ^ 4 := by rw [show 4 = 3 + 1 by norm_num, Nat.pow_add, Nat.mul_comm]; rw [mul_le_mul_left (by positivity)]; simp; omega
          rw [lt_iff_le_and_ne] at h₅
          tauto
        -- We have b ≤ 4.
        simp [hc] at h₀ h₁ h₂
        have h₁ : a ^ 3 - b ^ 3 > 1 := by
          calc
            a ^ 3 - b ^ 3 ≥ (b + 1) ^ 3 - b ^ 3 := by apply Nat.sub_le_sub_right; apply Nat.pow_le_pow_left (by omega)
            _ = 3 * b ^ 2 + 3 * b + 1 := by ring_nf; rw [Nat.add_sub_cancel]
            _ > 1 := by omega
        replace h₁ : a ^ 2 * b ^ 2 < a ^ 2 * (2 * a) := by
          calc
            a ^ 2 * b ^ 2 = a ^ 3 + (b ^ 3 + 1 ^ 3) := by rw [<-Nat.add_assoc, <-hc, h, hc]; ring
            _ < a ^ 3 + a ^ 3 := by apply add_lt_add_left; rw [Nat.add_comm]; apply Nat.add_lt_of_lt_sub; simp [h₁]
            _ = a ^ 2 * (2 * a) := by ring
        rw [mul_lt_mul_left (by positivity)] at h₁
        have h₅ : 4 * (1 + b ^ 3) > b ^ 4 := by
          calc
            4 * (1 + b ^ 3) = 4 * a ^ 2 * (b ^ 2 - a) := by rw [Nat.mul_assoc]; simp [<-h₂]; ac_rfl
            _ ≥ 4 * a ^ 2 * 1 := by rw [ge_iff_le, mul_le_mul_left (by positivity)]; omega
            _ = (2 * a) ^ 2 := by ring
            _ > (b ^ 2) ^ 2 := by apply Nat.pow_lt_pow_left h₁ (by norm_num)
            _ = b ^ 4 := by ring
        have hb' : b ≤ 4 := by
          by_contra! hb
          absurd h₅
          simp
          calc
            4 * (1 + b ^ 3) ≤ b ^ 3 + (b - 1) * b ^ 3 := by rw [Nat.mul_add]; apply add_le_add; refine (show 4 * 1 ≤ 5 ^ 3 by omega).trans ?_; apply pow_le_pow_left₀ (by norm_num) (by omega); rw [mul_le_mul_right]; omega; positivity
            _ ≤ b ^ 4 := by nth_rewrite 1 [show b ^ 3 = 1 * b ^ 3 by simp, <-add_mul, show b ^ 4 = b * b ^ 3 by ring]; rw [mul_le_mul_right]; omega; positivity
        subst hc
        -- Analyze the possible values of b.
        interval_cases b
        . -- When b = 1, 1 < a < b² yields contradiction.
          omega
        . -- When b = 2, 2 < a < b² gives a = 3.
          have h₆ : a = 3 := by
            omega
          subst h₆
          right
          right
          right
          right
          right
          trivial
        . -- When b = 3, consider cases 3 < a < b², each violating h.
          interval_cases a
          all_goals
            omega
        . -- When b = 4, consider cases 4 < a < b², each violating h.
          interval_cases a
          all_goals
            omega
  . -- Next, we show that the six triples are solutions.
    simp at h
    obtain h | h | h | h | h | h := h
    all_goals
      rw [h.1, h.2.1, h.2.2]
      norm_num