import Mathlib

set_option maxHeartbeats 500000
/- Find all 7-digit numbers formed by using only the digits 5 and 7 , and divisible by both 5 and 7 . -/
theorem number_theory_607806 :
    {n : ℕ | ∃ a b c d e f g: ℕ, (a = 5 ∨ a = 7) ∧ (b = 5 ∨ b = 7) ∧ (c = 5 ∨ c = 7) ∧ (d = 5 ∨ d = 7) ∧
    (e = 5 ∨ e = 7) ∧ (f = 5 ∨ f = 7) ∧ (g = 5 ∨ g = 7)
    ∧ n = a * 10^6 + b * 10^5 + c * 10^4 + d * 10^3 + e * 10^2 + f * 10 + g ∧ n % 5 = 0 ∧ n % 7 = 0} =
        {7775775, 7757575, 5577775, 7575575, 5777555, 7755755, 5755575, 5557755, 7555555} := by
    ext n
    constructor
    -- the forward direction
    . intro h
      simp only [Set.mem_setOf_eq] at h
      rcases h with ⟨a, b, c, d, e, f, g, ha, hb, hc, hd, he, hf, hg, hn, h1, h2⟩
      -- we show that f = 5
      have o: g ≠ 7 := by
        by_contra! o
        rw [hn] at h1
        replace h1: g % 5 = 0 := by omega
        rw [o] at h1
        tauto
      simp only [o] at hg
      simp at hg
      rw [hg] at hn
      rw [hn]
      by_contra! no
      simp at no
      absurd h2
      rw [hn]
      clear o hg h1 hn
      rcases no with ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9⟩  --simplify the condition
      replace o1: ¬ (a = 7 ∧ b = 7 ∧ c = 7 ∧ d = 5 ∧ e = 7 ∧ f = 7) := by
        by_contra! no
        simp [no] at o1
      replace o2: ¬ (a = 7 ∧ b = 7 ∧ c = 5 ∧ d = 7 ∧ e = 5 ∧ f = 7) := by
        by_contra! no
        simp [no] at o2
      replace o3: ¬ (a = 5 ∧ b = 5 ∧ c = 7 ∧ d = 7 ∧ e = 7 ∧ f = 7) := by
        by_contra! no
        simp [no] at o3
      replace o4: ¬ (a = 7 ∧ b = 5 ∧ c = 7 ∧ d = 5 ∧ e = 5 ∧ f = 7) := by
        by_contra! no
        simp [no] at o4
      replace o5: ¬ (a = 5 ∧ b = 7 ∧ c = 7 ∧ d = 7 ∧ e = 5 ∧ f = 5) := by
        by_contra! no
        simp [no] at o5
      replace o6: ¬ (a = 7 ∧ b = 7 ∧ c = 5 ∧ d = 5 ∧ e = 7 ∧ f = 5) := by
        by_contra! no
        simp [no] at o6
      replace o7: ¬ (a = 5 ∧ b = 7 ∧ c = 5 ∧ d = 5 ∧ e = 5 ∧ f = 7) := by
        by_contra! no
        simp [no] at o7
      replace o8: ¬ (a = 5 ∧ b = 5 ∧ c = 5 ∧ d = 7 ∧ e = 7 ∧ f = 5) := by
        by_contra! no
        simp [no] at o8
      replace o9: ¬ (a = 7 ∧ b = 5 ∧ c = 5 ∧ d = 5 ∧ e = 5 ∧ f = 5) := by
        by_contra! no
        simp [no] at o9

      have eq: (a * 10 ^ 6 + b * 10 ^ 5 + c * 10 ^ 4 + d * 10 ^ 3 + e * 10 ^ 2 + f * 10 + 5) % 7 =
      (a + b * 5 + c * 4 + d * 6 + 2 * e + 3 * f + 5) % 7 := by --simplify the expression
        clear *- ha
        norm_num
        simp [Nat.add_mod,← Nat.mul_mod_mod]
        simp
        ring_nf
      rw [eq]
      clear eq h2
      rcases ha with ha | ha  --check them way by a fast way
      all_goals simp [ha] at *
      all_goals rcases hb with hb | hb
      all_goals simp [hb] at *
      all_goals rcases hc with hc | hc
      all_goals simp [hc] at *
      all_goals rcases hd with hd | hd
      all_goals simp [hd] at *
      all_goals rcases he with he | he
      all_goals simp [he] at *
      all_goals rcases hf with hf | hf
      all_goals simp [hf] at *


   -- the backward direction

    . intro h
      simp at h
      rcases h with h | h | h | h | h | h | h | h | h
      all_goals simp [h]