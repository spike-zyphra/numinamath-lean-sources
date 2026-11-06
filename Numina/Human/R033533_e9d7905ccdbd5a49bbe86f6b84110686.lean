import Mathlib

open MeasureTheory intervalIntegral

theorem algebra_611369 : ∫ z in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, min x (min y z) = 1 / 4 := by
-- Prove that the integral of min function on $[0, 1]$ is $c - c^2 / 2$ for any $c$ in $[0, 1]$
  have aux1 : ∀ c : ℝ, 0 ≤ c → c ≤ 1 → ∫ x in (0 : ℝ)..1, min x c = c - c ^ 2 / 2 := by
    intro c cge cle
    have aux1 : IntervalIntegrable (fun x => min x c) volume 0 c := by
      apply Continuous.intervalIntegrable
      apply Continuous.min; exact continuous_id'; exact continuous_const
    have aux2 : IntervalIntegrable (fun x => min x c) volume c 1 := by
      apply Continuous.intervalIntegrable
      apply Continuous.min; exact continuous_id'; exact continuous_const
    rw [← integral_add_adjacent_intervals aux1 aux2]
    replace aux1 : Set.EqOn (fun x => min x c) (fun x => x) (Set.uIcc 0 c) := by
      intro x; simp [Set.mem_uIcc]
      intro h; rcases h with h|h
      · exact h.right
      have : c = 0 := by linarith
      rw [this]; exact h.right
    replace aux2 : Set.EqOn (fun x => min x c) (fun _ => c) (Set.uIcc c 1) := by
      intro x; simp [Set.mem_uIcc]
      intro h; rcases h with h|h
      · exact h.left
      have : c = 1 := by linarith
      rw [this]; exact h.left
    rw [integral_congr aux1, integral_congr aux2]
    simp; ring
-- Rewrite the goal by `integral_congr aux1`
  replace aux1 : Set.EqOn (fun z => ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
  min x (min y z)) (fun z => ∫ y in (0 : ℝ)..1, min y z - (min y z) ^ 2 / 2) (Set.uIcc 0 1) := by
    intro z; simp; intro zge zle
    apply integral_congr
    intro y; simp; intro yge yle
    apply aux1; exact le_min yge zge
    exact inf_le_of_right_le zle
  rw [integral_congr aux1]
-- Compute the double integral in question by splitting the inner one at $z$
  have aux2 : ∀ z : ℝ, 0 ≤ z → z ≤ 1 → ∫ (y : ℝ) in (0 : ℝ)..1, y ⊓ z - (y ⊓ z) ^ 2 / 2 =
  z - z ^ 2 + z ^ 3 / 3 := by
    intro z zge zle
    have aux1 : IntervalIntegrable (fun y => y ⊓ z - (y ⊓ z) ^ 2 / 2) volume 0 z := by
      apply Continuous.intervalIntegrable
      apply Continuous.sub; apply Continuous.min
      exact continuous_id'; exact continuous_const
      apply Continuous.div_const; apply Continuous.pow
      apply Continuous.min; exact continuous_id'; exact continuous_const
    have aux2 : IntervalIntegrable (fun y => y ⊓ z - (y ⊓ z) ^ 2 / 2) volume z 1 := by
      apply Continuous.intervalIntegrable
      apply Continuous.sub; apply Continuous.min
      exact continuous_id'; exact continuous_const
      apply Continuous.div_const; apply Continuous.pow
      apply Continuous.min; exact continuous_id'; exact continuous_const
    rw [← integral_add_adjacent_intervals aux1 aux2]
    replace aux1 : Set.EqOn (fun y => y ⊓ z - (y ⊓ z) ^ 2 / 2) (fun y => y - y ^ 2 / 2) (Set.uIcc 0 z) := by
      intro x; simp [Set.mem_uIcc]
      intro h; rcases h with h|h
      · rw [min_eq_left]; exact h.right
      have : z = 0 ∧ x = 0 := ⟨by linarith, by linarith⟩
      simp [this.left, this.right]
    replace aux2 : Set.EqOn (fun y => y ⊓ z - (y ⊓ z) ^ 2 / 2) (fun _ => z - z ^ 2 / 2) (Set.uIcc z 1) := by
      intro x; simp [Set.mem_uIcc]
      intro h; rcases h with h|h
      · rw [min_eq_right]; exact h.left
      have : z = 1 ∧ x = 1 := ⟨by linarith, by linarith⟩
      simp [this.left, this.right]
    rw [integral_congr aux1, integral_congr aux2]
    simp; ring
-- Rewrite the goal by `integral_congr aux2` and the goal follows from `norm_num`
  replace aux2 : Set.EqOn (fun z => ∫ y in (0 : ℝ)..1, min y z - (min y z) ^ 2 / 2) (fun z =>
  z - z ^ 2 + z ^ 3 / 3) (Set.uIcc 0 1) := by
    intro z; simp; apply aux2
  rw [integral_congr aux2]; norm_num