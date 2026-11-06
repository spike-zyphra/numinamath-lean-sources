import Mathlib

theorem number_theory_57905 {s : Set ℕ} (hs : s = {d : ℕ | ∃p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∈ Set.Ioo 4 18 ∧ q ∈ Set.Ioo 4 18 ∧ d = p * q - (p + q)}) : 21 ∉ s ∧ 60 ∉ s∧ 119 ∈ s ∧ 180 ∉ s ∧ 231 ∉ s := by
  rw [hs]
  constructor
  · -- Show 21 ∉ s
    intro h
    rcases h with ⟨p, q, hp, hq, hneq, hp1, hq1, heq⟩
    rcases hp1 with ⟨hp11, hp12⟩
    rcases hq1 with ⟨hq11, hq12⟩
    interval_cases p <;> interval_cases q 
      <;> norm_num at hp hq hneq hp11 hp12 hq11 hq12 
      <;> omega
  constructor 
  · -- Show 60 ∉ s 
    intro h
    rcases h with ⟨p, q, hp, hq, hneq, hp1, hq1, heq⟩
    rcases hp1 with ⟨hp11, hp12⟩
    rcases hq1 with ⟨hq11, hq12⟩
    interval_cases p <;> interval_cases q 
      <;> norm_num at hp hq hneq hp11 hp12 hq11 hq12 
      <;> omega
  constructor
  · -- Show 119 ∈ s 
    use 11, 13 
    all_goals
      norm_num 
  constructor
  · -- Show 180 ∉ s 
    intro h
    rcases h with ⟨p, q, hp, hq, hneq, hp1, hq1, heq⟩
    rcases hp1 with ⟨hp11, hp12⟩
    rcases hq1 with ⟨hq11, hq12⟩
    interval_cases p <;> interval_cases q 
      <;> norm_num at hp hq hneq hp11 hp12 hq11 hq12 
      <;> omega 
  · -- Show 231 ∉ s 
    intro h
    rcases h with ⟨p, q, hp, hq, hneq, hp1, hq1, heq⟩
    rcases hp1 with ⟨hp11, hp12⟩
    rcases hq1 with ⟨hq11, hq12⟩
    interval_cases p <;> interval_cases q 
      <;> norm_num at hp hq hneq hp11 hp12 hq11 hq12 
      <;> omega