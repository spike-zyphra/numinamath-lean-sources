import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat
/-Find the three-digit positive integer  $\underline{a} \ \underline{b} \ \underline{c}$  whose representation in base nine is  $\underline{b} \ \underline{c} \ \underline{a}_{\hspace{.02in}\text{nine}}$ , where  $a$ ,  $b$ , and  $c$  are (not necessarily distinct) digits.-/
theorem number_theory_8750 (a b c : ℤ) (h : a ≠ 0) (h₀ : 0 ≤ a ∧ a ≤ 8) (h₁ : 0 ≤ b ∧ b ≤ 8) (h₂ : 0 ≤ c ∧ c ≤ 8) (h₃ : 100 * a + 10 * b + c = 81 * b + 9 * c + a) : a = 2 ∧ b = 2 ∧ c = 7 := by
  have ha1 : 0 ≤ a := h₀.1
  have ha2 : a ≤ 8 := h₀.2
  have hb1 : 0 ≤ b := h₁.1
  have hb2 : b ≤ 8 := h₁.2
  have hc1 : 0 ≤ c := h₂.1
  have hc2 : c ≤ 8 := h₂.2
  have h : 99 * a = 71 * b + 8 * c := by
    calc
    _ = 100 * a + 10 * b + c - 10 * b - c - a := by ring
    _ = 81 * b + 9 * c + a - 10 * b - c - a := by rw [h₃]
    _ = _ := by ring
  interval_cases a
  interval_cases b
  interval_cases c
  repeat' omega
--It's easily to prove by checking every number from $100$ to $999$. Then we can know that $a = 2,\ b = 2, \ c = 7$.
