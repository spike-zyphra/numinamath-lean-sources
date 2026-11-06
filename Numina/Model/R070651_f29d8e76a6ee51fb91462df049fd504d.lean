import Mathlib

theorem algebra_6362 (S : Finset ℕ) (hS : S = Finset.Icc 1 2017) :
    S.card = 1 → ∃ x ∈ S, x = 2035153 := by
  rintro h
  have h1 : S.card = 2017 := by
    rw [hS]
    native_decide
  rw [h1] at h
  exfalso
  try { linarith }
  all_goals
    try { 
      have h2 : 2017 = 1 := by linarith
      norm_num at h2 ⊢ 
    }
    <;> try { contradiction }
    <;> try { native_decide }
    <;> try { tauto }
    <;> try { omega }
    <;> try { linarith }
    <;> try { contradiction }
    <;> try { native_decide }
    <;> try { tauto }
    <;> try { omega }
    <;> try { linarith }
    <;> try { contradiction }
    <;> try { native_decide }
    <;> try { tauto }
    <;> try { omega }
    <;> try { linarith }
    <;> try { contradiction }
    <;> try { native_decide }
    <;> try { tauto }
    <;> try { omega }
    <;> try { linarith }
    <;> try { contradiction }
    <;> try { native_decide }
    <;> try { tauto }
    <;> try { omega }
    <;> try { linarith }
    <;> try { contradiction }
    <;> try { native_decide }
    <;> try { tauto }
    <;> try { omega }