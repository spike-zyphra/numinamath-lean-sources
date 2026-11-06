import Mathlib

open Real

/- Given that $a+b+c=5$ and that $1 \leq a, b, c \leq 2$, what is the minimum possible value of $\frac{1}{a+b}+\frac{1}{b+c}$ ? -/
theorem algebra_608561:
  (∀ a b c : ℝ, a + b + c = 5 ∧ (1 ≤ a ∧ a ≤ 2) ∧ (1 ≤ b ∧ b ≤ 2) ∧ (1 ≤ c ∧ c ≤ 2) → (1/(a+b)+1/(b+c) ≥ 4/7))
  ∧ (∃ a b c : ℝ, a+b+c = 5 ∧ (1 ≤ a ∧ a ≤ 2) ∧ (1 ≤ b ∧ b ≤ 2)  ∧ (1 ≤ c ∧ c ≤ 2) ∧ 1/(a+b)+1/(b+c) = 4/7) := by
  constructor
  . -- prove that 4/7 is minimum value
    let f := λ a b c: ℝ => 1/(a+b)+1/(b+c)

    -- prove when b = 2, f a b c ≥ 4/7
    have h1: ∀ a b c : ℝ, a + b + c = 5 → (1 ≤ a ∧ a ≤ 2) → b=2 → (1 ≤ c ∧ c ≤ 2) → (f a b c ≥ 4/7) := by
      intro a b c hsum ha hb hc

      -- disturb b, 1 / (a + 2) + 1 / (2 + c) ≥ 4 / 7
      simp only [f, hb]

      calc 1 / (a+2) + 1/(2+c)
        = (a+c+4) / ((a+2)* (2+c)) := by
            rw [div_add_div] ; all_goals try linarith
            simp
            rw [← add_assoc, div_left_inj']
            linarith
            simp ; constructor; all_goals linarith
        _ = 7 / ((a+2)*(c+2)) := by
            have hac: a+c = 3 := by linarith
            rw [hac]; norm_num [add_comm]
        _ ≥ 4/7 := by
            have hc: c = 3 - a := by linarith
            rw [hc, ge_iff_le, sub_add_eq_add_sub] ; norm_num
            have : (5-a) > 0 := by linarith
            have : (a+2) > 0 := by linarith
            have : (a+2)*(5-a) > 0 := by positivity
            rw [le_div_iff₀', mul_comm, ← le_div_iff₀']; all_goals try positivity
            field_simp ; norm_num
            let u := a - 3/2
            have hu : a = u + 3/2 := by simp [u]
            rw [hu, add_assoc, sub_add_eq_sub_sub_swap, add_comm] ; norm_num
            rw [← sq_sub_sq]; norm_num
            positivity

    intro a b c h
    let ⟨hsum, ha, hb, hc⟩ := h

    by_cases hb1: b = 2

    -- when b = 2, we can use previous lemma.
    . apply h1 a b c h.1 h.2.1 hb1 h.2.2.2

    -- when b < 2, a > 1, we can decrease the sum by decreasing a and increasing b. make b' = 2 and a' = a + b - 2
    let a' := a + b - 2
    have hab : a' + 2 = a + b := by simp [a']

    -- we can show that f a b c ≥ f a' 2 c
    have h2: f a b c ≥ f a' 2 c := by
      -- notice that 1/a'+2=1/(a+b), so we only needs to compare 1/(b+c) and 1/(b'+c), where b'=2
      simp [hab, f]
      -- b ≤ 2 → 1/(b+c)≥1/(b'+c)
      rw [inv_le_inv₀] ; all_goals try linarith

    -- It can be shown that a'+b'+c = 5
    have h3: a' + 2 + c = 5 := by
      linarith [h.1, hab]

    -- and 1 ≤ a' ∧ a' ≤ 2
    have h4: 1 ≤ a' ∧ a' ≤ 2 := by
      constructor ; all_goals try linarith

    -- so f a b c ≥ f a' 2 c ≥ 4/7
    calc f a b c ≥ f a' 2 c := by exact h2
        _ ≥ (4/7: ℝ) := by
          apply h1
          exact h3
          exact h4
          rfl
          exact hc

  . -- prove that 4/7 is possible value
    use 3/2, 2, 3/2
    norm_num
