import Mathlib
import Aesop
open BigOperators
set_option maxHeartbeats 500000

/- Let  $a,b$  be positive integers. Prove that   $$ \min(\gcd(a,b+1),\gcd(a+1,b))\leq\frac{\sqrt{4a+4b+5}-1}{2} $$   When does the equality hold? -/
theorem number_theory_8692 {a b : ℕ} (h₀ : 0 < a) (h₁ : 0 < b) :
    min (Nat.gcd a (b + 1)) (Nat.gcd (a + 1) b) ≤ (Real.sqrt (4 * a + 4 * b + 5) - 1) / 2 ∧ ((∃ d : ℕ, d ≥ 2 ∧ ((a, b) = (d, d ^ 2 - 1) ∨ (b, a) = (d, d ^ 2 - 1))) ↔ min (Nat.gcd a (b + 1)) (Nat.gcd (a + 1) b) = (Real.sqrt (4 * a + 4 * b + 5) - 1) / 2) := by
  -- Step 1: Let d₁ = gcd(a, b + 1) and d₂ = gcd(a + 1, b) and simplify the problem.
  let d₁ : ℕ := Nat.gcd a (b + 1)
  let d₂ : ℕ := Nat.gcd (a + 1) b
  suffices min d₁ d₂ ≤ (Real.sqrt (4 * a + 4 * b + 5) - 1) / 2 ∧ ((∃ d : ℕ, d ≥ 2 ∧ ((a, b) = (d, d ^ 2 - 1) ∨ (b, a) = (d, d ^ 2 - 1))) ↔ min d₁ d₂ = (Real.sqrt (4 * a + 4 * b + 5) - 1) / 2) by
    rw [show Nat.gcd a (b + 1) = d₁ by rfl, show Nat.gcd (a + 1) b = d₂ by rfl]
    tauto
  -- Step 2a: d₁ divides a + b + 1 because d₁ divides a and b + 1.
  have g₁ : d₁ ∣ a + b + 1 := by
    apply Nat.dvd_add (show d₁ ∣ a by apply Nat.gcd_dvd_left) (show d₁ ∣ b + 1 by apply Nat.gcd_dvd_right)
  -- Step 2b: d₂ divides a + b + 1 because d₂ divides b and (a + 1).
  have g₂ : d₂ ∣ a + b + 1 := by
    rw [add_assoc, add_comm, add_assoc]
    nth_rewrite 2 [add_comm]
    apply Nat.dvd_add (show d₂ ∣ b by apply Nat.gcd_dvd_right) (show d₂ ∣ a + 1 by apply Nat.gcd_dvd_left)
  -- Step 3: d₁ and d₂ are coprime, hence their product d₁ * d₂ also divides a + b + 1.
  have g₃ : Nat.gcd d₁ d₂ = 1 := by
    calc
      Nat.gcd d₁ d₂ = Nat.gcd (Nat.gcd a (b + 1)) (Nat.gcd (a + 1) b) := by simp
      _ = Nat.gcd (Nat.gcd a (a + 1)) (Nat.gcd b (b + 1)) := by rw [Nat.gcd_assoc, Nat.gcd_comm (b + 1) (Nat.gcd (a + 1) b), Nat.gcd_assoc, <-Nat.gcd_assoc]
      _ = 1 := by simp [Nat.gcd_rec a (a + 1)]
  have g₄ : d₁ * d₂ ∣ a + b + 1 := by
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
    assumption'
  refine ⟨?_, ?_⟩
  . -- First show the inequality holds.
    by_cases h : d₁ = d₂
    . -- Case 1: d₁ = d₂.
      have g₅ : d₁ = 1 := by
        rw [<-Nat.gcd_self d₁]
        nth_rewrite 2 [h]
        rw [g₃]
      have g₆ : (9 : ℝ) ≤ 4 * a + 4 * b + 5 := by
        rw [show (9 : ℝ) = (9 : ℕ) by simp, show (4 * a + 4 * b + 5 : ℝ) = (4 * a + 4 * b + 5 : ℕ) by simp, Nat.cast_le]
        omega
      calc
        min d₁ d₂ = (1 : ℝ) := by rw [<-h, g₅]; simp
        _ ≤ (Real.sqrt 9 - 1) / 2 := by rw [show (9 : ℝ) = 3 ^ 2 by norm_num]; simp; norm_num
        _ ≤ (Real.sqrt (4 * a + 4 * b + 5) - 1) / 2 := by linarith [show Real.sqrt 9 ≤ Real.sqrt (4 * a + 4 * b + 5) from Real.sqrt_le_sqrt g₆]
    . -- Case 2 : d₁ ≠ d₂.
      apply Nat.lt_or_gt_of_ne at h
      -- WLOG: If x < y and x * y ≤ a + b + 1, then min x y ≤ (Real.sqrt (4 * a + 4 * b + 5) - 1) / 2.
      have lm (x y : ℕ) (hxy : x < y) (g : x * y ≤ a + b + 1) : min x y ≤ (Real.sqrt (4 * a + 4 * b + 5) - 1) / 2 := by
        -- Boring calculations.
        have g₇ : x + 1 ≤ y := by omega
        replace g₇ : (x + 1 : ℝ) ≤ y := by
          rwa [show (y : ℝ) = (y : ℕ) by simp, show (x + 1 : ℝ) = (x + 1 : ℕ) by simp, Nat.cast_le]
        replace g₇ : (x * (x + 1) : ℝ) ≤ a + b + 1 := by
          rw [show (a + b + 1 : ℝ) = (a + b + 1 : ℕ) by simp, show (x * (x + 1) : ℝ) = (x * (x + 1) : ℕ) by simp, Nat.cast_le]
          nlinarith
        replace g₇ : (2 * x + 1 : ℝ) ^ 2 ≤ 4 * a + 4 * b + 5 := by
          calc
            (2 * x + 1 : ℝ) ^ 2 = (4 * (x + (1 : ℝ) / 2) ^ 2 : ℝ) := by ring_nf
            _ ≤ 4 * a + 4 * b + 5 := by rw [show (x + (1 : ℝ) / 2) ^ 2 = x * (x + 1 : ℝ) + 1 / 4 by ring_nf]; linarith
        replace g₇ : 2 * x + (1 : ℝ) ≤ Real.sqrt (4 * a + 4 * b + 5) := by
          rw [<-@Real.sqrt_sq (2 * x + 1 : ℝ)]
          apply Real.sqrt_le_sqrt g₇
          linarith [show (0 : ℝ) ≤ x by norm_num]
        calc
          min x y ≤ (x : ℝ) := by rw [show ↑(min x y) = ((min x y) : ℕ) by simp, show (x : ℝ) = (x : ℕ) by simp, Nat.cast_le]; apply Nat.min_le_left
          _ ≤ (Real.sqrt (4 * a + 4 * b + 5) - 1) / 2 := by linarith
      -- We can apply the lemma either when d₁ < d₂ or when d₁ > d₂.
      obtain h | h' := h
      . -- When d₁ < d₂.
        apply lm
        assumption
        apply Nat.le_of_dvd
        linarith
        assumption
      . -- When d₂ < d₁.-/
        rw [min_comm]
        apply lm
        assumption
        apply Nat.le_of_dvd
        linarith
        rwa [Nat.mul_comm]
  . -- Now show the condition for equality.
    apply Iff.intro -- Break the iff into two implications.
    . -- If d ≥ 2 and {a, b} = {d, d ^ 2 - 1}, then the equality is attained.
      -- WLOG : If a = d and b = d ^ 2 - 1, the equality is attained.
      have lm (a b : ℕ) (h₀ : 0 < a) (h₁ : 0 < b) (h : ∃ d : ℕ, d ≥ 2 ∧ (a, b) = (d, d ^ 2 - 1)) : min (Nat.gcd a (b + 1)) (Nat.gcd (a + 1) b) = (Real.sqrt (4 * a + 4 * b + 5) - 1) / 2 := by
        obtain ⟨d, ⟨hd, hab⟩⟩ := h
        obtain _ | _ := hab -- Substitute a = d and b = d ^ 2 - 1 into the expressions.
        clear h₀
        have g₅ : (a ^ 2 - 1 : ℕ) = (a ^ 2 - 1 : ℝ) := by
          -- We have to show a ^ 2 - 1 make sense by a ^ 2 > 0.
          norm_cast
          rw [Int.subNatNat_of_le]
          omega
        have g₆ : a ^ 2 - 1 + 1 = a * a := by
          rw [Nat.sub_one_add_one]
          ring_nf
          omega
        calc
          (↑(min (Nat.gcd a (a ^ 2 - 1 + 1)) (Nat.gcd (a + 1) (a ^ 2 - 1))) : ℝ) = (↑(min (a.gcd (a * a)) ((a + 1).gcd ((a + 1) * (a - 1)))) : ℝ) := by norm_cast; rw [g₆, <-Nat.sq_sub_sq, show a.gcd (a * a) = Nat.gcd a (a * a) by rfl, show Nat.gcd (a + 1) (a ^ 2 - 1) = (a + 1).gcd (a ^ 2 - 1) by rfl]
          _ = (↑(min a (a + 1)) : ℝ) := by rw [Nat.gcd_mul_right_right a a, Nat.gcd_mul_right_right (a - 1) (a + 1)]
          _ = (a : ℝ) := by norm_num
          _ = (Real.sqrt (4 * a ^ 2 + 4 * a + 1) - 1) / 2 := by field_simp; rw [show (4 * a ^ 2 + 4 * a + 1 : ℝ) = (4 * a ^ 2 + 4 * a + 1 : ℕ) by norm_num, show 4 * a ^ 2 + 4 * a + 1 = (2 * a + 1) ^ 2 by ring_nf]; simp; rw [Real.sqrt_sq]; ring_nf; linarith
          _ = (Real.sqrt (4 * a + 4 * (a ^ 2 - 1 : ℝ) + 5) - 1) / 2 := by ring_nf
          _ = (Real.sqrt (4 * a + 4 * (a ^ 2 - 1 : ℕ) + 5) - 1) / 2 := by rw [g₅]
      -- Now prove the real goal.
      intro ⟨d, hd⟩
      obtain ⟨hd, h⟩ := hd
      obtain h | h := h
      . -- When a = d and b = d ^ 2 - 1, apply the lemma directly.
        apply lm
        tauto
        repeat assumption
      . -- When b = d and a = d ^ 2 - 1, apply the lemma with a and b swapped.
        rw [min_comm]
        rw [show d₂ = b.gcd (a + 1) by rw [Nat.gcd_comm]]
        rw [show d₁ = (b + 1).gcd a by rw [Nat.gcd_comm]]
        rw [show (4 * a + 4 * b + 5 : ℝ) = 4 * b + 4 * a + 5 by ring_nf]
        apply lm b a
        tauto
        repeat assumption
    . -- If the equality holds, then {a, b} = {d, d ^ 2 - 1} for some d ≥ 2.
      intro eq
      -- First prove that d₁ ≠ d₂.
      have h : d₁ ≠ d₂ := by
        by_contra h -- Prove by contradiction.
        have g₅ : d₁ = 1 := by
          rw [<-Nat.gcd_self d₁]
          nth_rewrite 2 [h]
          rw [g₃]
        have g₆ : (9 : ℝ) < 4 * a + 4 * b + 5 := by
          rw [show (9 : ℝ) = (9 : ℕ) by simp, show (4 * a + 4 * b + 5 : ℝ) = (4 * a + 4 * b + 5 : ℕ) by simp, Nat.cast_lt]
          omega
        replace g₆ : Real.sqrt 9 < Real.sqrt (4 * a + 4 * b + 5) := by
          apply Real.sqrt_lt_sqrt
          norm_num
          exact g₆
        have _ : (↑(min d₁ d₂) : ℝ) < (↑(min d₁ d₂) : ℝ) := by
          calc
            min d₁ d₂ = (1 : ℝ) := by rw [<-h, g₅]; simp
            _ ≤ (Real.sqrt 9 - 1) / 2 := by rw [show (9 : ℝ) = 3 ^ 2 by norm_num]; simp; norm_num
            _ < (Real.sqrt (4 * a + 4 * b + 5) - 1) / 2 := by linarith
            _ = min d₁ d₂ := by symm; exact eq
        linarith
      apply Nat.lt_or_gt_of_ne at h
      -- WLOG : If d₁ < d₂ and the equality holds, then (a, b) = (d₁, d₁ ^ 2 - 1) where d₁ ≥ 2.
      have lm (a b d₁ d₂ : ℕ) (h₀ : 0 < a) (h₁ : 0 < b) (hd₁ : d₁ = a.gcd (b + 1)) (hd₂ : d₂ = (a + 1).gcd b) (g₃ : d₁.gcd d₂ = 1) (g₄ : d₁ * d₂ ∣ a + b + 1) (eq : min d₁ d₂ = (Real.sqrt (4 * a + 4 * b + 5) - 1) / 2) (h : d₁ < d₂) : (a, b) = (d₁, d₁ ^ 2 - 1) := by
        rw [min_eq_left (show d₁ ≤ d₂ by linarith)] at eq
        replace eq : 2 * d₁ + 1 = Real.sqrt (4 * a + 4 * b + 5) := by
          field_simp at eq
          linarith
        replace eq : (2 * d₁ + 1) ^ 2 = 4 * a + 4 * b + 5 := by
          rify
          rw [eq, Real.sq_sqrt]
          linarith
        replace eq : d₁ * (d₁ + 1) = a + b + 1 := by
          ring_nf at eq
          linarith
        -- Step 1: show that d₂ = d₁ + 1.
        apply Nat.le_sub_one_of_lt at h
        have g₅ : d₂ = d₂ - 1 + 1 := by
          rw [Nat.sub_one_add_one]
          have _ : d₂ > 0 := by
            rw [hd₂]
            apply Nat.gcd_pos_of_pos_left
            linarith
          linarith
        replace h : d₁ + 1 ≤ d₂ := by
          rw [Nat.add_one, g₅, Nat.add_one]
          apply Nat.succ_le_succ
          exact h
        apply Nat.le_of_dvd at g₄
        have _ : a + b + 1 ≤ d₁ * d₂ := by
          by_contra!
          have eq_false : d₁ * (d₁ + 1) < a + b + 1 := by
            calc
              d₁ * (d₁ + 1) ≤ d₁ * d₂ := by nlinarith
              _ < a + b + 1 := by assumption
          linarith
        replace g₄ : d₁ * d₂ = a + b + 1 := by
          linarith
        have _ : d₂ ≤ d₁ + 1 := by
          by_contra!
          have eq_false : d₁ * (d₁ + 1) < a + b + 1 := by
            calc
              d₁ * (d₁ + 1) < d₁ * d₂ := by nlinarith
              _ = a + b + 1 := by assumption
          linarith
        replace h : d₂ = d₁ + 1 := by
          linarith
        -- Step 2: show that d₁ > 0, so that d₁ - 1 + 1 = d₁.
        rw [h] at g₃
        have hd₁_pos : d₁ > 0 := by
          by_contra!
          have g : d₁ = 0 := by
            linarith
          rw [g] at eq
          ring_nf at eq
          linarith
        -- Step 3: show that a ≡ d₁ (mod d₁(d₁ + 1)).
        have hmod_a : a ≡ Nat.chineseRemainder g₃ 0 d₁ [MOD (d₁ * (d₁ + 1))] := by
          apply Nat.chineseRemainder_modEq_unique
          apply Dvd.dvd.modEq_zero_nat
          rw [hd₁]
          apply Nat.gcd_dvd_left
          apply Nat.ModEq.add_right_cancel' 1
          have g : d₁ + 1 ∣ a + 1 := by
            rw [<-h, hd₂]
            apply Nat.gcd_dvd_left
          calc
            a + 1 ≡ 0 [MOD (d₁ + 1)] := by apply Dvd.dvd.modEq_zero_nat; exact g
            _ ≡ 0 + (d₁ + 1) [MOD (d₁ + 1)] := by symm; apply Nat.add_modEq_right
            _ = d₁ + 1 := by ring_nf
        have g : d₁ ≡ Nat.chineseRemainder g₃ 0 d₁ [MOD (d₁ * (d₁ + 1))] := by
          apply Nat.chineseRemainder_modEq_unique
          apply Dvd.dvd.modEq_zero_nat
          apply Nat.dvd_refl
          exact Nat.ModEq.rfl
        symm at g
        replace hmod_a : a ≡ d₁ [MOD (d₁ * (d₁ + 1))] := by
          apply Nat.ModEq.trans hmod_a g
        clear g
        -- Step 4: show that b ≡ d₁ ^ 2 - 1 (mod d₁(d₁ + 1)).
        have hmod_b : b ≡ Nat.chineseRemainder g₃ (d₁ - 1) (d₁ + 1) [MOD (d₁ * (d₁ + 1))] := by
          apply Nat.chineseRemainder_modEq_unique
          apply Nat.ModEq.add_right_cancel' 1
          rw [Nat.sub_one_add_one]
          have g : d₁ ∣ b + 1 := by
            rw [hd₁]
            apply Nat.gcd_dvd_right
          calc
            b + 1 ≡ 0 [MOD d₁] := by apply Dvd.dvd.modEq_zero_nat; exact g
            _ ≡ 0 + d₁ [MOD d₁] := by symm; apply Nat.add_modEq_right
            _ = d₁ := by ring_nf
          linarith
          rw [<-h]
          calc
            b ≡ 0 [MOD d₂] := by apply Dvd.dvd.modEq_zero_nat; rw [hd₂]; apply Nat.gcd_dvd_right
            _ ≡ 0 + d₂ [MOD d₂] := by symm; apply Nat.add_modEq_right
            _ = d₂ := by ring_nf
        have g : d₁ ^ 2 - 1 ≡ Nat.chineseRemainder g₃ (d₁ - 1) (d₁ + 1) [MOD (d₁ * (d₁ + 1))] := by
          apply Nat.chineseRemainder_modEq_unique
          have g₅ : d₁ ^ 2 - 1 = d₁ - 1 + d₁ * (d₁ - 1) := by
            ring_nf
            nth_rewrite 2[<-Nat.one_mul (d₁ - 1)]
            rw [<-Nat.add_mul, <-Nat.sq_sub_sq]
            omega
          rw [g₅]
          nth_rewrite 3 [(show d₁ - 1 = d₁ - 1 + 0 by omega)]
          apply Nat.ModEq.add_left (d₁ - 1)
          apply Dvd.dvd.modEq_zero_nat
          apply Nat.dvd_mul_right -- or simp
          replace g₅ : d₁ ^ 2 - 1 = (d₁ + 1) * (d₁ - 1) := by
            rw [<-Nat.sq_sub_sq]
          rw [g₅]
          calc
            (d₁ + 1) * (d₁ - 1) ≡ 0 [MOD (d₁ + 1)] := by apply Dvd.dvd.modEq_zero_nat; apply Nat.dvd_mul_right
            _ ≡ 0 + (d₁ + 1) [MOD (d₁ + 1)] := by symm; apply Nat.add_modEq_right
            _ = d₁ + 1 := by ring_nf
        symm at g
        replace hmod_b : b ≡ d₁ ^ 2 - 1 [MOD (d₁ * (d₁ + 1))] := by
          apply Nat.ModEq.trans hmod_b g
        clear g
        -- Step 5: show that a ≥ d₁ and b ≥ d₁ ^ 2 - 1.
        have lm (a b n : ℕ) (h₀ : 0 < n) (h₁ : b < n) (h₂ : a ≡ b [MOD n]) : a ≥ b := by
          have g₆ : a % n ≡ b [MOD n] := by
            calc
              a % n ≡ a [MOD n] := by apply Nat.mod_modEq
              _ ≡ b [MOD n] := by exact h₂
          apply Nat.ModEq.eq_of_lt_of_lt at g₆
          have g₇ : a % n < n := by
            apply Nat.mod_lt
            assumption
          rw [ge_iff_le]
          simp [g₇, h₁] at g₆
          calc
            b = a % n := by rw [g₆]
            _ ≤ a := by apply Nat.mod_le
        have g₆ : a ≥ d₁ := by
          apply lm a d₁ (d₁ * (d₁ + 1))
          nlinarith
          nlinarith
          exact hmod_a
        have g₇ : b ≥ d₁ ^ 2 - 1 := by
          apply lm b (d₁ ^ 2 - 1) (d₁ * (d₁ + 1))
          nlinarith
          calc
            d₁ ^ 2 - 1 = (d₁ - 1) * (d₁ + 1) := by rw [Nat.mul_comm, <-Nat.sq_sub_sq]
            _ < (d₁ - 1 + 1) * (d₁ + 1) := by nlinarith
            _ = d₁ * (d₁ + 1) := by rw [Nat.sub_one_add_one]; linarith
          exact hmod_b
        have _ : a ≤ d₁ ∧ b ≤ d₁ ^ 2 - 1 := by
          by_contra g
          replace g : d₁ < a ∨ d₁ ^ 2 - 1 < b := by
            rw [Decidable.not_and_iff_or_not] at g
            simp at g
            assumption
          rw [h] at g₄
          have wg₄ : a + b + 1 > d₁ * (d₁ + 1) := by
            obtain g | g := g
            . -- If a > d₁, we derive a contradiction.
              calc
                a + b + 1 > d₁ + b + 1 := by linarith
                _ ≥ d₁ + (d₁ ^ 2 - 1) + 1 := by linarith
                _ = d₁ + d₁ ^ 2 := by rw [Nat.add_assoc, Nat.sub_one_add_one]; linarith -- does not work using nlinarith
                _ = d₁ * (d₁ + 1) := by ring_nf
            . -- If b > d₁ ^ 2 - 1, we also derive a contradiction.
              calc
                a + b + 1 > a + (d₁ ^ 2 - 1) + 1 := by linarith
                _ ≥ d₁ + (d₁ ^ 2 - 1) + 1 := by linarith
                _ = d₁ + d₁ ^ 2 := by rw [Nat.add_assoc, Nat.sub_one_add_one]; linarith
                _ = d₁ * (d₁ + 1) := by ring_nf
          linarith
        rw [show a = d₁ by omega, show b = d₁ ^ 2 - 1 by omega]
        linarith -- show that 0 < a + b + 1 to complete the proof
      obtain h | h' := h
      . -- Case 1: d₁ < d₂ (and the equality holds).
        use d₁
        have g₅ : (a, b) = (d₁, d₁ ^ 2 - 1) := by
          apply lm a b d₁ d₂
          all_goals
            try assumption
            try simp
        have g₆ : d₁ ≥ 2 := by
          by_contra! g
          interval_cases d₁
          -- When d₁ = 0, we derive a contradiction.
          linarith only [h₀, show a = 0 by omega]
          -- When d₁ = 1, we derive a contradiction.
          have _ : b = 0 := by
            calc
              b = (a, b).2 := by simp
              _ = (1, 1 ^ 2 - 1).2 := by rw[g₅]
              _ = 0 := by omega
          linarith
        tauto
      . -- Case 2 : d₂ < d₁ (and the equality holds).
        use d₂
        have g₅ : (b, a) = (d₂, d₂ ^ 2 - 1) := by
          apply lm b a d₂ d₁
          rw [Nat.mul_comm, Nat.add_comm b a]
          assumption
          rw [min_comm]
          rw [show (4 * b + 4 * a + 5 : ℝ) = 4 * a + 4 * b + 5 by ring_nf]
          assumption'
          rw [Nat.gcd_comm]
          rw [Nat.gcd_comm]
          rw [Nat.gcd_comm]
          assumption
        have g₆ : d₂ ≥ 2 := by
          by_contra! g
          interval_cases d₂
          -- When d₂ = 0, we derive a contradiction.
          linarith [h₀, show b = 0 by omega]
          -- When d₂ = 1, we derive a contradiction.
          have _ : a = 0 := by
            calc
              a = (b, a).2 := by simp
              _ = (1, 1 ^ 2 - 1).2 := by rw [g₅]
              _ = 0 := by omega
          linarith
        tauto
