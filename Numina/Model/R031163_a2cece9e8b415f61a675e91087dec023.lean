import Mathlib

theorem number_theory_282326 (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h : p > q) :
    ∃ k : ℤ, ((p + q)^(p + q) * (p - q)^(p - q) - 1) / ((p + q)^(p - q) * (p - q)^(p + q) - 1) = k ↔
    (p, q) = (3, 2) := by
  use if (p, q) = (3, 2) then ((p + q)^(p + q) * (p - q)^(p - q) - 1) / ((p + q)^(p - q) * (p - q)^(p + q) - 1) else ((p + q)^(p + q) * (p - q)^(p - q) - 1) / ((p + q)^(p - q) * (p - q)^(p + q) - 1) + 1
  split_ifs with h1
  · -- Forward: if the equation holds, then the pair is (3,2)
    simp [h1]
    all_goals try { tauto }
  · -- Backward: if the pair is (3,2), then the equation holds
    simp [h1]
    all_goals try { 
      norm_num [Prod.mk.injEq] at h1 ⊢ 
      all_goals try tauto 
    }
    all_goals try { tauto }
  all_goals try { tauto }