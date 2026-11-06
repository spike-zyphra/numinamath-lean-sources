import Mathlib

open Multiset

/--Michael has 16 white socks, 3 blue socks, and 6 red socks in a drawer. Ever the lazy college student, he has overslept and is late for his favorite team's season-opener. Because he is now in such a rush to get from Harvard to Foxborough, he randomly takes socks from the drawer (one at a time) until he has a pair of the same color. What is the largest number of socks he could possibly withdraw in this fashion?-/

abbrev color := Fin 3 -- 0 for white, 1 for blue, 2 for red

def miachel_socks : Multiset color := (replicate 16 (0 : color)) +  (replicate 3 (1 : color)) +  (replicate 6 (2 : color))

-- #eval miachel_socks

theorem combinatorics_608162 : IsGreatest { n : ℕ | ∃ socks : Multiset color, Subset socks miachel_socks ∧ socks.card = n.pred ∧ socks.Nodup} 4 := by
  simp[IsGreatest, miachel_socks]
  constructor
  · use {0, 1, 2}
    simp
  · simp[upperBounds]
    intros n socks h1 h2 h3
    by_contra!

    have h4 : (4:ℕ).pred < n.pred := Nat.pred_lt_pred (show 4 ≠ 0 by norm_num) this
    norm_num at h4
    rw [← h2] at h4
    
    have h5 : (socks.toFinset).card = socks.card :=
      Multiset.toFinset_card_of_nodup h3

    have h6 : (socks.toFinset).card ≤ 3 := calc
      (socks.toFinset).card ≤ Fintype.card color := Finset.card_le_univ (socks.toFinset)
      _ = 3 := by rw [Fintype.card_fin] 
    rw [h5] at h6
    linarith
