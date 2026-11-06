import Mathlib

theorem algebra_73070 {G : Type*} [Group G] (a : G) :
    ∃ H : Subgroup G, H = {x | ∃ n : ℤ, x = a ^ n} := by 
  use { carrier := {x | ∃ n : ℤ, x = a ^ n},
        one_mem' := by 
          use 0 
          simp 
        , mul_mem' := by 
          intro x y hx hy 
          rcases hx with ⟨m, hm⟩ 
          rcases hy with ⟨n, hn⟩ 
          use m + n 
          simp [hm, hn, zpow_add] 
        , inv_mem' := by 
          intro x hx 
          rcases hx with ⟨n, hn⟩ 
          use -n 
          simp [hn, zpow_neg] 
      }
  all_goals 
    ext x 
    simp