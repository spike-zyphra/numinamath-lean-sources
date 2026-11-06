import Mathlib

open Finset

theorem number_theory_72614 {f : ℕ → ℕ}
    (hf1 : f 1 = 1)
    (hfn : ∀ n > 1, f n = sSup {p | p.Prime ∧ p ∣ n}) :
    ∃ n > 0, ¬∃ a v : ℕ,
      a > 0 ∧ v > 0 ∧
      a ≤ n ∧ v ≤ n ∧
      a > v ∧
      ¬∃ m > 0, m ≤ f a ∧ m ≥ 1 ∧ v - m > 0 := by
  use 1
  constructor
  · norm_num
  · intro h
    rcases h with ⟨a, v, ha, hv, hale, hvle, hagt, hnoneed⟩
    have h1 : a = 1 := by linarith
    have h2 : v = 1 := by linarith
    linarith