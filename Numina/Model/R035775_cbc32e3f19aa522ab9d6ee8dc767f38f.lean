import Mathlib

theorem algebra_172236 {a : ℕ → ℝ} (ha : ∀ n, a (n + 1) = (a n + a 1) / (a n + 1)) :
    (a 1 = -3 → a 2020 = -3) ∧ (a 1 = 2 → ∀ n ≥ 2, 4 / 3 ≤ a n ∧ a n ≤ 3 / 2) := by 
  constructor
  · -- Proof for part (a)
    intro ha1
    have ha1' : a 1 = -3 := ha1
    have h1 : ∀ k : ℕ, a (3 * k + 1) = -3 := by
      intro k
      induction k with
      | zero =>
        norm_num [ha1']
      | succ k ih =>
        have eq1 : a (3 * (k + 1) + 1) = (a (3 * (k + 1) ) + a 1) / (a (3 * (k + 1) ) + 1) := ha (3 * (k + 1) )
        have eq21 : a (3 * (k + 1) ) = 0 := by
          have eq211 : a (3 * k + 3) = 0 := by
            have eq2111 : a (3 * k + 3) = (a (3 * k + 2) + a 1) / (a (3 * k + 2) + 1) := ha (3 * k + 2)
            have eq22 : a (3 * k + 2) = 3 := by
              have eq311 : a (3 * k + 2) = (a (3 * k + 1) + a 1) / (a (3 * k + 1) + 1) := ha (3 * k + 1)
              rw [show a (3 * k + 1) = -3 by simpa using ih] at eq311
              rw [ha1'] at eq311
              norm_num at eq311 ⊢
              linarith
            rw [eq22, ha1'] at eq2111
            norm_num at eq2111 ⊢
            linarith
          have eq212 : 3 * (k + 1) = 3 * k + 3 := by omega
          rw [eq212]
          linarith
        rw [eq21, ha1'] at eq1
        norm_num at eq1 ⊢
        linarith
    specialize h1 673
    norm_num at h1 ⊢
    linarith
  · -- Proof for part (b)
    intro ha1
    intro n hn
    have h1 : ∀ (k : ℕ), a (k + 2) = (a (k + 1) + a 1) / (a (k + 1) + 1) := by 
      intro k
      have h2' : a ((k + 1) + 1) = (a (k + 1) + a 1) / (a (k + 1) + 1) := by 
        specialize ha (k + 1)
        simpa using ha
      simpa using h2'
    have h3 : ∀ (k : ℕ), 4 / 3 ≤ a (k + 2) ∧ a (k + 2) ≤ 3 / 2 := by 
      intro k
      induction' k using Nat.strongRecOn with k ih
      cases k with
      | zero =>
        have ha2 : a 2 = 4 / 3 := by
          specialize h1 0
          rw [ha1] at h1
          norm_num at h1 ⊢
          all_goals
            linarith
        constructor
        · -- Show lower bound
          linarith [ha2]
        · -- Show upper bound
          linarith [ha2]
      | succ k =>
        have ha_eq : a ((k + 1) + 2) = (a (k + 2) + a 1) / (a (k + 2) + 1) := by 
          specialize h1 (k + 1)
          simpa using h1
        have ha_eq2 : a 1 = (2 : ℝ) := by linarith [ha1]
        have h11 : 4 / 3 ≤ a (k + 2) ∧ a (k + 2) ≤ 3 / 2 := by 
          specialize ih k (by linarith)
          simpa using ih
        rw [ha_eq, ha_eq2]
        constructor
        · -- Show lower bound
          have h10 : 4 / 3 ≤ a (k + 2) := by linarith [h11.1]
          have h12 : a (k + 2) ≤ 3 / 2 := by linarith [h11.2]
          apply (le_div_iff₀ (by nlinarith)).mpr
          nlinarith
        · -- Show upper bound
          have h10 : 4 / 3 ≤ a (k + 2) := by linarith [h11.1]
          have h12 : a (k + 2) ≤ 3 / 2 := by linarith [h11.2]
          apply (div_le_iff₀ (by nlinarith)).mpr
          nlinarith
    have h4 : n - 2 ≥ (0 : ℕ) := by omega
    specialize h3 (n - 2)
    have h5 : a n = a ((n - 2) + 2) := by 
      cases n with
      | zero => linarith -- impossible by hn
      | succ n => 
        cases n with 
        | zero => linarith -- impossible by hn
        | succ n => 
          simp [Nat.add_sub_cancel_left]
    rw [show a n = a ((n - 2) + 2) by linarith [h5]]
    simpa using h3