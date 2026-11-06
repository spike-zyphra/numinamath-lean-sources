import Mathlib


theorem Algebra_604504 {a b : ℕ → ℤ} (ha₀ : a 0 = 0) (hb₀ : b 0 = 8) (ha : ∀ (n : ℕ), a (n + 2) = 2 * a (n + 1) - a n + 2)
  (hb : ∀ n, b (n + 2) = 2 * b (n + 1) - b n) : 
  ∃ (A B A' B': ℤ), (A ≠ A') ∧ ((((a 1 = A + 1) ∧ (b 1 = B + 8)) → (∀ (n : ℕ), ∃ (k : ℤ), ((a n) ^ 2 + (b n) ^ 2 = k ^ 2)) ) 
  ∧  (((a 1 = A' + 1) ∧ (b 1 = B' + 8)) → (∀ (n : ℕ), ∃ (k : ℤ), ((a n) ^ 2 + (b n) ^ 2 = k ^ 2)))) := by 
    -- use induction to prove this general formula of `a_n` and `b_n`
    have an_ind (n : ℕ):  a n = (n : ℤ) ^ 2 + ((a 1) - 1) * (n : ℤ) := by 
      induction n using Nat.strongRecOn with
      | _ n ih =>
        obtain _ | _ | _ | n := n
        · simpa -- case 0
        · simp -- case 1
        · -- case 2
          simp
          obtain ha' := ha 0
          simp at ha'
          rw [ha']
          ring_nf
          rw [ha₀]
          simp
        · -- induction step
          have eq_aux : n + 1 + 1 + 1 = (n + 1) + 2 := by ring
          rw [eq_aux]
          obtain ha' := ha (n + 1)
          rw [ha']
          obtain ha_eq := ih (n + 1) (by linarith)
          obtain ha_eq' := ih (n + 1 + 1) (by linarith)
          rw [ha_eq, ha_eq']
          have eq_aux' : 2 * (↑(n + (1 : ℤ) + 1) ^ 2 + (a 1 - 1) * ↑(n + (1 : ℤ) + 1)) - (↑(n + (1 : ℤ)) ^ 2 + (a 1 - 1) * ↑(n + (1 : ℤ))) + 2 =
          ↑(n + (1 : ℤ) + 2) ^ 2 + (a 1 - 1) * ↑(n + (1 : ℤ) + 2) := by ring
          norm_cast
    have bn_ind (n : ℕ):  b n = (b 1 -8) * n + 8 := by
      induction n using Nat.strongRecOn with
      | _ n ih =>
        obtain _ | _ | _ | n := n
        · simpa -- case 0
        · simp -- case 1
        · -- case 2
          simp
          obtain hb' := hb 0
          simp at hb'
          rw [hb']
          ring_nf
          rw [hb₀]
          ring
        · -- induction step
          have eq_aux : n + 1 + 1 + 1 = (n + 1) + 2 := by ring
          rw [eq_aux]
          obtain hb' := hb (n + 1)
          rw [hb']
          obtain hb_eq := ih (n + 1) (by linarith)
          obtain hb_eq' := ih (n + 1 + 1) (by linarith)
          rw [hb_eq, hb_eq']
          have eq_aux' : 2 * ((b 1 - 8) * ↑(n + (1 : ℤ) + 1) + 8) - ((b 1 - 8) * ↑(n + (1 : ℤ)) + 8) = (b 1 - 8) * ↑(n + (1 : ℤ) + 2) + 8 := by ring
          norm_cast
    use 4
    use 4
    use -4 
    use -4
    constructor -- to prove `A ≠ A'` , namely we have two cases
    simp
    constructor
    · -- first case, namely `A = 4`
      intro h n
      use (n ^ 2 + 4 * n + 8)
      obtain ⟨h₁, h₂⟩ := h
      obtain an_ind := an_ind n
      obtain bn_ind := bn_ind n
      rw [h₁] at an_ind
      simp at an_ind
      rw [h₂] at bn_ind
      simp at bn_ind
      rw [an_ind, bn_ind]
      ring
    · -- second case, namely `A' = 4`
      intro h n
      use (n ^ 2 - 4 * n + 8)
      obtain ⟨h₁, h₂⟩ := h
      obtain an_ind := an_ind n
      obtain bn_ind := bn_ind n
      rw [h₁] at an_ind
      simp at an_ind
      rw [h₂] at bn_ind
      simp at bn_ind
      rw [an_ind, bn_ind]
      ring