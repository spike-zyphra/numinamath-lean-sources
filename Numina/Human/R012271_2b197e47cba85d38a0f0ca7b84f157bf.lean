import Mathlib
open Nat Real Finset Set
noncomputable section

/-Let $a, b, c$ be distinct positive integers, then the minimum value of $\frac{abc}{a+b+c}$ is ______.-/
theorem number_theory_600028 : IsLeast { q | ∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a ≠ b ∧ b ≠ c ∧
  a ≠ c ∧ q = (a * b * c : ℚ) / (a + b + c) } 1 := by
  unfold IsLeast
  -- IsLeast requires proving $1 ∈ S ∧ ∀ q ∈ S$, $1 ≤ q$.
  constructor
  · -- Subgoal $1$: Prove $1 ∈ S$, i.e., there exist $a$, $b$, $c$ such that $q = 1$.
    use 1, 2, 3
    norm_num
  · -- Subgoal $2$: Prove $∀ q ∈ S$, $1 ≤ q$.
    intro q hq
    rcases hq with ⟨a, b, c, ha, hb, hc, hab, hbc, hac, hq_eq⟩
    have h_abc_pos : (a * b * c : ℚ) > 0 := by exact_mod_cast Nat.cast_pos.mpr (mul_pos (mul_pos ha hb) hc)
    have h_sum_pos : (a + b + c : ℚ) > 0 := by
      have : 0 < (a + b + c : ℚ) := by exact_mod_cast Nat.cast_pos.mpr (Nat.add_pos_left (Nat.add_pos_left ha b) c)
      exact this
    have h_recip_ineq : (1 / (a * b) + 1 / (b * c) + 1 / (c * a) : ℚ) ≤ 1 / 2 + 1 / 6 + 1 / 3 := by
      -- Without loss of generality, assume $a < b < c$, and prove the target holds.
      wlog h_ab : a < b
      · -- case : $a < b$.
        have h_ab' : b < a := by omega
        have h_abc_pos' : (b * a * c : ℚ) > 0 := by linarith
        have h_sum_pos' : (b + a + c : ℚ) > 0 := by linarith
        have hq_eq': q = ↑b * ↑a * ↑c / (↑b + ↑a + ↑c) :=by
          norm_cast
          have h₁ : ↑b * ↑a * ↑c =  ↑a * ↑b * ↑c := by ring
          have h₂ : ↑b + ↑a + ↑c =  ↑a + ↑b + ↑c := by ring
          rw [h₁, h₂]
          exact_mod_cast hq_eq
        have h_ba := this b a c hb ha hc hab.symm hac hbc hq_eq'
        have h_symm : (1 / (b * a) + 1 / (a * c) + 1 / (c * b) : ℚ) = (1 / (a * b) + 1 / (b * c) + 1 / (c * a) : ℚ) := by
          simp [mul_comm]
          ring
        rw [← h_symm]
        exact h_ba h_abc_pos' h_sum_pos' h_ab'
      · -- case : $a < b$.
        wlog h_bc : b < c
        · -- case : $b > c$.
          have h_bc' : c < b := by omega
          have h_abc_pos' : (a * c * b : ℚ) > 0 := by linarith
          have h_sum_pos' : (a + c + b : ℚ) > 0 := by linarith
          have hq_eq' : q = ↑a * ↑c * ↑b / (↑a + ↑c + ↑b) := by
            norm_cast
            have h₁ : ↑a * ↑c * ↑b = ↑a * ↑b * ↑c := by ring
            have h₂ : ↑a + ↑c + ↑b = ↑a + ↑b + ↑c := by ring
            rw [h₁, h₂]
            exact_mod_cast hq_eq
          have h_cb := this a c b ha hc hb hac hbc.symm hab hq_eq'
          have h_symm : (1 / (a * c) + 1 / (c * b) + 1 / (b * a) : ℚ) = (1 / (a * b) + 1 / (b * c) + 1 / (c * a) : ℚ) := by
            simp [mul_comm]
            ring
          by_cases h_ac : a < c
          · -- subcase : $a < c$.
            rw [← h_symm]
            exact h_cb h_abc_pos' h_sum_pos' h_ac h_bc'
          · -- subcase : $a > c$.
            have h_ac' : c < a := by omega
            have h_abc_pos'' : (c * a * b : ℚ) > 0 := by linarith
            have h_sum_pos'' : (c + a + b : ℚ) > 0 := by linarith
            have hq_eq'' : q = ↑c * ↑a * ↑b / (↑c + ↑a + ↑b) := by
              norm_cast
              have h₁ : ↑c * ↑a * ↑b = ↑a * ↑b * ↑c := by ring
              have h₂ : ↑c + ↑a + ↑b = ↑a + ↑b + ↑c := by ring
              rw [h₁, h₂]
              exact_mod_cast hq_eq
            have h_cb' := this c a b hc ha hb hac.symm hab hbc.symm hq_eq''
            have h_symm' : (1 / (c * a) + 1 / (a * b) + 1 / (b * c) : ℚ) = (1 / (a * b) + 1 / (b * c) + 1 / (c * a) : ℚ) := by
              simp [mul_comm]
              ring
            rw [← h_symm']
            exact h_cb' h_abc_pos'' h_sum_pos'' h_ac' h_ab
        · -- case : $a < b < c$ .
          have h_min_vals : a ≥ 1 ∧ b ≥ 2 ∧ c ≥ 3 := by
            have h_a : a ≥ 1 := by nlinarith
            have h_b : b ≥ 2 := by nlinarith
            have h_c : c ≥ 3 := by nlinarith
            exact ⟨h_a, h_b, h_c⟩
          have h_denom_bounds : a * b ≥ 2 ∧ b * c ≥ 6 ∧ c * a ≥ 3 := by
            exact ⟨Nat.mul_le_mul h_min_vals.1 h_min_vals.2.1, Nat.mul_le_mul h_min_vals.2.1 h_min_vals.2.2,
                  Nat.mul_le_mul h_min_vals.2.2 h_min_vals.1⟩
          have h_ineq : (1 / (a * b) + 1 / (b * c) + 1 / (c * a) : ℚ) ≤ 1 / 2 + 1 / 6 + 1 / 3 := by
            have h₁: (1 : ℚ) / (a * b) ≤ 1 / 2 := by
              have h₁₂ : (a * b : ℚ) ≥ 2 := by exact_mod_cast h_denom_bounds.1
              have h₁₃ : (1 : ℚ) / (a * b) ≤ 1 / 2 := by
                rw [div_le_div_iff₀ (by positivity) (by positivity)]
                nlinarith
              exact h₁₃
            have h₂: (1 : ℚ) / (b * c) ≤ 1 / 6 := by
              have h₂₂ : (b * c : ℚ) ≥ 6 := by exact_mod_cast h_denom_bounds.2.1
              have h₂₃ : (1 : ℚ) / (b * c) ≤ 1 / 6 := by
                rw [div_le_div_iff₀ (by positivity) (by positivity)]
                nlinarith
              exact h₂₃
            have h₃: (1 : ℚ) / (c * a) ≤ 1 / 3 := by
              have h₃₂ : (c * a : ℚ) ≥ 3 := by exact_mod_cast h_denom_bounds.2.2
              have h₃₃ : (1 : ℚ) / (c * a) ≤ 1 / 3 := by
                rw [div_le_div_iff₀ (by positivity) (by positivity)]
                nlinarith
              exact h₃₃
            have h₄ : (1 / (a * b) + 1 / (b * c) + 1 / (c * a) : ℚ) ≤ 1 / 2 + 1 / 6 + 1 / 3 := by
              exact add_le_add (add_le_add h₁ h₂) h₃
            exact h₄
          exact h_ineq
    -- Based on the above inequality, transform the target to prove $(a * b * c : ℚ) / (a + b + c) ≥ 1$.
    have h_recip_sum : (a + b + c : ℚ) / (a * b * c) = (1 / (a * b) + 1 / (b * c) + 1 / (c * a)) := by
      field_simp [h_abc_pos, h_sum_pos]
      ring
    have h_bound : (a + b + c : ℚ) / (a * b * c) ≤ 1 := by nlinarith
    have h_bound' : (a + b + c : ℚ) ≤ (a * b * c) := by
      apply (div_le_one h_abc_pos).mp
      exact h_bound
    have h_bound'' : (a * b * c)  / (a + b + c : ℚ) ≥  1 := by
      apply (one_le_div h_sum_pos).mpr
      exact h_bound'
    have h_q_ge_one : q ≥ 1 := by
      rw [hq_eq]
      exact h_bound''
    exact h_q_ge_one
