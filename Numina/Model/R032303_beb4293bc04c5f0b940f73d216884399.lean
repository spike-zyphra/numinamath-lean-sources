import Mathlib

theorem number_theory_15057 :
    IsGreatest {k | ∃ x, k = {i | i ∈ Finset.range 49 ∧ (x + i) % 7 = 0}.ncard} 7 := by
  constructor
  · -- Show 7 is in the set
    use 0
    have : {i | i ∈ Finset.range 49 ∧ (0 + i) % 7 = 0} = Finset.filter (fun i => i % 7 = 0) (Finset.range 49) := by
      ext i 
      simp
    rw [this]
    rw [Set.ncard_coe_Finset]
    native_decide
  · -- Show any element in the set ≤ 7
    intro k hk 
    rcases hk with ⟨x, hx⟩
    have h4 : {i | i ∈ Finset.range 49 ∧ (x + i) % 7 = 0} = ↑(Finset.filter (fun i => (x + i) % 7 = 0) (Finset.range 49)) := by
      ext i
      simp
    have h5 : (Finset.filter (fun i => (x + i) % 7 = 0) (Finset.range 49)).card = 7 := by
      have : (Finset.filter (fun i => (x + i) % 7 = 0) (Finset.range 49)).card = 7 := by
        have h3 : x % 7 = 0 ∨ x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 3 ∨ x % 7 = 4 ∨ x % 7 = 5 ∨ x % 7 = 6 := by 
          omega
        rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3)
        · -- Case 1: x % 7 = 0
          have hx6 : x % 7 = 0 := h3
          have hx7 : (Finset.filter (fun i => (x + i) % 7 = 0) (Finset.range 49)).card = 7 := by
            have h5 : (Finset.filter (fun i => (x + i) % 7 = 0) (Finset.range 49)) =
                Finset.filter (fun i => (i : Nat) % 7 = 0) (Finset.range 49) := by
              ext i
              simp [Nat.add_mod, hx6]
              <;> omega
            rw [h5]
            native_decide
          exact hx7
        · -- Case 2: x % 7 = 1
          have hx6 : x % 7 = 1 := h3
          have hx7 : (Finset.filter (fun i => (x + i) % 7 = 0) (Finset.range 49)).card = 7 := by
            have h5 : (Finset.filter (fun i => (x + i) % 7 = 0) (Finset.range 49)) =
                Finset.filter (fun i => (i : Nat) % 7 = 6) (Finset.range 49) := by
              ext i
              simp [Nat.add_mod, hx6]
              <;> omega
            rw [h5]
            native_decide
          exact hx7
        · -- Case 3: x % 7 = 2
          have hx6 : x % 7 = 2 := h3
          have hx7 : (Finset.filter (fun i => (x + i) % 7 = 0) (Finset.range 49)).card = 7 := by
            have h5 : (Finset.filter (fun i => (x + i) % 7 = 0) (Finset.range 49)) =
                Finset.filter (fun i => (i : Nat) % 7 = 5) (Finset.range 49) := by
              ext i
              simp [Nat.add_mod, hx6]
              <;> omega
            rw [h5]
            native_decide
          exact hx7
        · -- Case 4: x % 7 = 3
          have hx6 : x % 7 = 3 := h3
          have hx7 : (Finset.filter (fun i => (x + i) % 7 = 0) (Finset.range 49)).card = 7 := by
            have h5 : (Finset.filter (fun i => (x + i) % 7 = 0) (Finset.range 49)) =
                Finset.filter (fun i => (i : Nat) % 7 = 4) (Finset.range 49) := by
              ext i
              simp [Nat.add_mod, hx6]
              <;> omega
            rw [h5]
            native_decide
          exact hx7
        · -- Case 5: x % 7 = 4
          have hx6 : x % 7 = 4 := h3
          have hx7 : (Finset.filter (fun i => (x + i) % 7 = 0) (Finset.range 49)).card = 7 := by
            have h5 : (Finset.filter (fun i => (x + i) % 7 = 0) (Finset.range 49)) =
                Finset.filter (fun i => (i : Nat) % 7 = 3) (Finset.range 49) := by
              ext i
              simp [Nat.add_mod, hx6]
              <;> omega
            rw [h5]
            native_decide
          exact hx7
        · -- Case 6: x % 7 = 5
          have hx6 : x % 7 = 5 := h3
          have hx7 : (Finset.filter (fun i => (x + i) % 7 = 0) (Finset.range 49)).card = 7 := by
            have h5 : (Finset.filter (fun i => (x + i) % 7 = 0) (Finset.range 49)) =
                Finset.filter (fun i => (i : Nat) % 7 = 2) (Finset.range 49) := by
              ext i
              simp [Nat.add_mod, hx6]
              <;> omega
            rw [h5]
            native_decide
          exact hx7
        · -- Case 7: x % 7 = 6
          have hx6 : x % 7 = 6 := h3
          have hx7 : (Finset.filter (fun i => (x + i) % 7 = 0) (Finset.range 49)).card = 7 := by
            have h5 : (Finset.filter (fun i => (x + i) % 7 = 0) (Finset.range 49)) =
                Finset.filter (fun i => (i : Nat) % 7 = 1) (Finset.range 49) := by
              ext i
              simp [Nat.add_mod, hx6]
              <;> omega
            rw [h5]
            native_decide
          exact hx7
      exact this
    have h7 : {i | i ∈ Finset.range 49 ∧ (x + i) % 7 = 0}.ncard ≤ 7 := by
      have h8 : {i | i ∈ Finset.range 49 ∧ (x + i) % 7 = 0} = ↑(Finset.filter (fun i => (x + i) % 7 = 0) (Finset.range 49)) := h4
      rw [h8] 
      rw [Set.ncard_coe_Finset]
      all_goals 
      omega 
    have h8 : k = {i | i ∈ Finset.range 49 ∧ (x + i) % 7 = 0}.ncard := by
      exact hx
    linarith [h7, h8]