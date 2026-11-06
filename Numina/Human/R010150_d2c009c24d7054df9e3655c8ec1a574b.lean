import Mathlib

theorem number_theory_275817 : {n : ℕ | n < 1000 ∧ 8 ∣ 764000 + n ∧ 9 ∣ 764000 + n ∧ 11 ∣ 764000 + n} = {280} := by
  ext n
  simp
  constructor
  · intro ⟨h₁, h₂, h₃⟩
    omega
  intro h
  subst h
  exact ⟨by norm_num, by norm_num, by norm_num⟩
