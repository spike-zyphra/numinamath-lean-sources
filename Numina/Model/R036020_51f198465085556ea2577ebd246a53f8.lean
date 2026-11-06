import Mathlib

theorem algebra_16124 : IsGreatest {x : ℕ | ∃ a : Fin 4 → ℕ, (∀ i, 0 < a i) ∧ ∑ i, a i = 46 ∧
    (∃ d, ∀ i, a i = a 0 + i.val * d) ∧ x = a 2} 15 := by
  constructor
  · -- Show that 15 can be achieved
    use λ i => match i with
      | 0 => 1
      | 1 => 8
      | 2 => 15
      | 3 => 22
      | _ => 0
    constructor
    · intro i
      fin_cases i <;> simp
    constructor
    · simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    constructor
    · use 7
      intro i
      fin_cases i <;> simp
    · rfl
  · -- Show that 15 is the greatest
    intro x hx
    rcases hx with ⟨a, ha_pos, ha_sum, ⟨d, ha_arith⟩, hx⟩
    have h1 : a 0 = a 0 := by linarith
    have h2 : a 1 = a 0 + d := by
      have h2 := ha_arith 1
      simpa using h2
    have h3 : a 2 = a 0 + 2 * d := by
      have h3 := ha_arith 2
      simpa using h3
    have h4 : a 3 = a 0 + 3 * d := by
      have h4 := ha_arith 3
      simpa using h4
    have ha_sum' : a 0 + a 1 + a 2 + a 3 = 46 := by
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at ha_sum ⊢
      linarith
    rw [h2, h3, h4] at ha_sum'
    have h5 : 4 * a 0 + 6 * d = 46 := by linarith
    have h5_simplified : 2 * a 0 + 3 * d = 23 := by
      omega
    have hx' : x = a 0 + 2 * d := by
      linarith [h3]
    have h1 : a 0 > 0 := by
      specialize ha_pos 0
      linarith
    have h2 : a 1 > 0 := by
      specialize ha_pos 1
      linarith
    have h3_pos : a 2 > 0 := by
      specialize ha_pos 2
      linarith
    have h4_pos : a 3 > 0 := by
      specialize ha_pos 3
      linarith
    omega