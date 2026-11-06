import Mathlib

theorem algebra_313440 (d : ℕ) (h₀ : d > 0) (h₁ : ∃ n, d / n = n ∧ n > 0)
    (h₂ : d / 2 = 11 - 1 * (d / 4)) :
    d = 16 := by
  have h₃ : d ≤ 15 := by
    omega
  interval_cases d <;> omega
  <;> try { contradiction }
    <;> norm_num at h₁ h₂ <;> try { trivial }
    <;> try { tauto }
  all_goals
    omega
  <;> tauto
  <;> try { contradiction }
  <;> try { tauto }
  all_goals
    norm_num
  <;> try { tauto }
  <;> try { try { trivial } }
    <;> try { tauto }
  all_goals
    omega
  <;> try { trivial } <;> try { tauto }
  all_goals
    omega
  <;> try { trivial } <;> try { norm_num at h₁ }
  all_goals
    try { omega } <;> try { tauto } <;> norm_num at h₁ h₂ <;> omega
    <;> try { omega } <;> try { contradiction }
  all_goals
    omega
  <;> try { trivial } <;> try { tauto }
  all_goals
    omega
  <;> try { trivial } <;> try { tauto }
  all_goals
    omega
  <;> try { trivial }
  all_goals
    try { try { omega } } <;> try { tauto }
    <;> try { try { trivial } }